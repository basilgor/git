#include "cache.h"
#include "run-command.h"
#include "pkt-line.h"
#include "string-list.h"
#include "vcs-cvs/cvs-client.h"
#include "vcs-cvs/trace-utils.h"
#include "vcs-cvs/cvs-cache.h"

#include <string.h>

/*
 * TODO:
 * rework full_module_path, should not end with /
 */

static const char trace_key[] = "GIT_TRACE_CVS_PROTO";
static const char trace_proto[] = "CVS";
extern unsigned long fileMemoryLimit;
extern int dumb_rlog;

size_t cvs_written_total = 0;
size_t cvs_read_total = 0;

/*
 * [:method:][[user][:password]@]hostname[:[port]]/path/to/repository
 */

static void strbuf_copybuf(struct strbuf *sb, const char *buf, size_t len)
{
	sb->len = 0;

	strbuf_grow(sb, len + 1);
	strncpy(sb->buf, buf, len);
	sb->len = len;
	sb->buf[len] = '\0';
}

static inline void strbuf_copy(struct strbuf *sb, struct strbuf *sb2)
{
	strbuf_copybuf(sb, sb2->buf, sb2->len);
}

static inline void strbuf_copystr(struct strbuf *sb, const char *str)
{
	strbuf_copybuf(sb, str, strlen(str));
}

static int parse_cvsroot(struct cvs_transport *cvs, const char *cvsroot)
{
	const char *idx = 0;
	const char *next_tok = cvsroot;
	const char *colon;

	/*
	 * parse connect method
	 */
	if (cvsroot[0] == ':') {
		next_tok = cvsroot + 1;
		idx = strchr(next_tok, ':');
		if (!idx)
			return -1;

		if (!strncmp(next_tok, "ext", 3))
			cvs->protocol = cvs_proto_ext;
		else if (!strncmp(next_tok, "local", 5))
			cvs->protocol = cvs_proto_local;
		else if (!strncmp(next_tok, "pserver", 7))
			cvs->protocol = cvs_proto_pserver;

		next_tok = idx + 1;
	}
	else if (cvsroot[0] != '/')
		cvs->protocol = cvs_proto_ext;

	/*
	 * parse user/password
	 */
	idx = strchr(next_tok, '@');
	if (idx) {
		colon = strchr(next_tok, ':');
		if (colon < idx) {
			cvs->username = xstrndup(next_tok, colon - next_tok);
			next_tok = colon + 1;
			cvs->password = xstrndup(next_tok, idx - next_tok);
		}
		else {
			cvs->username = xstrndup(next_tok, idx - next_tok);
		}

		next_tok = idx + 1;
	}

	/*
	 * parse host/port
	 */
	idx = strchr(next_tok, ']');
	if (!idx) {
		idx = strchr(next_tok, ':');
		if (!idx) {
			idx = strchr(next_tok, '/');
			if (!idx)
				return -1;
		}
	}
	else {
		++idx;
	}

	cvs->host = xstrndup(next_tok, idx - next_tok);
	next_tok = idx;

	if (cvs->host[0] == '[') {
		memmove(cvs->host, cvs->host + 1, strlen(cvs->host) - 2);
		cvs->host[strlen(cvs->host) - 2] = '\0';
	}

	if (*idx == '\0')
		return -1;

	/*
	 * FIXME: check dos drive prefix?
	 */
	if (*idx == ':') {
		char *port;
		next_tok = idx + 1;

		if (*next_tok != '/') {
			idx = strchr(next_tok, '/');
			if (!idx)
				return -1;

			port = xstrndup(next_tok, idx - next_tok);
			cvs->port = atoi(port);
			free(port);

			if (!cvs->port)
				return -1;

			next_tok = idx;
			if (*next_tok == ':')
				next_tok++;
		}
	}

	/*
	 * the rest is server repo path
	 */
	cvs->repo_path = xstrdup(next_tok);
	if (cvs->repo_path[strlen(cvs->repo_path)] == '/')
		cvs->repo_path[strlen(cvs->repo_path)] = '\0';

	if (!cvs->port) {
		switch (cvs->protocol) {
		case cvs_proto_ext:
			cvs->port = 22;
			break;
		case cvs_proto_pserver:
			cvs->port = 2401;
			break;
		default:
			break;
		}
	}

	return 0;
}

static struct child_process no_fork;

struct child_process *cvs_init_transport(struct cvs_transport *cvs,
				  const char *prog, int flags)
{
	struct child_process *conn = &no_fork;
	const char **arg;
	struct strbuf sport = STRBUF_INIT;
	struct strbuf host = STRBUF_INIT;

	/* Without this we cannot rely on waitpid() to tell
	 * what happened to our children.
	 */
	signal(SIGCHLD, SIG_DFL);

	if (cvs->protocol == cvs_proto_pserver) {
		if (index(cvs->host, ':'))
			strbuf_addf(&host, "[%s]:%hu", cvs->host, cvs->port);
		else
			strbuf_addf(&host, "%s:%hu", cvs->host, cvs->port);
		git_tcp_connect(cvs->fd, host.buf, flags);
		strbuf_release(&host);
		return conn;
	}

	conn = xcalloc(1, sizeof(*conn));
	conn->in = conn->out = -1;
	conn->argv = arg = xcalloc(7, sizeof(*arg));
	if (cvs->protocol == cvs_proto_ext) {
		const char *ssh = getenv("GIT_SSH");
		int putty = ssh && strcasestr(ssh, "plink");
		if (!ssh) ssh = "ssh";

		*arg++ = ssh;
		if (putty && !strcasestr(ssh, "tortoiseplink"))
			*arg++ = "-batch";
		if (cvs->port) {
			strbuf_addf(&sport, "%hu", cvs->port);

			/* P is for PuTTY, p is for OpenSSH */
			*arg++ = putty ? "-P" : "-p";
			*arg++ = sport.buf;
		}

		if (cvs->username)
			strbuf_addf(&host, "%s@", cvs->username);
		strbuf_addstr(&host, cvs->host);
		*arg++ = host.buf;
	}
	else {
		/* remove repo-local variables from the environment */
		//conn->env = local_repo_env;
		conn->use_shell = 1;
	}
	*arg++ = prog;
	*arg = NULL;

	if (start_command(conn))
		die("unable to fork");

	cvs->fd[0] = conn->out; /* read from child's stdout */
	cvs->fd[1] = conn->in;  /* write to child's stdin */

	strbuf_release(&sport);
	strbuf_release(&host);
	return conn;
}

static ssize_t z_write_in_full(int fd, git_zstream *wr_stream, const void *buf, size_t len)
{
	unsigned char zbuf[ZBUF_SIZE];
	unsigned long zlen;
	ssize_t written = 0;
	ssize_t ret;
	int flush = Z_NO_FLUSH;

	wr_stream->next_in = (void *)buf;
	wr_stream->avail_in = len;
	wr_stream->avail_out = sizeof(zbuf);

	while (wr_stream->avail_in ||
	//       !wr_stream->avail_out ||
	       flush == Z_NO_FLUSH) {

		wr_stream->next_out = zbuf;
		wr_stream->avail_out = sizeof(zbuf);

		if (git_deflate_bound(wr_stream, wr_stream->avail_in) <= sizeof(zbuf))
			flush = Z_SYNC_FLUSH;

		if (git_deflate(wr_stream, flush) != Z_OK)
			die("deflate failed");

		zlen = sizeof(zbuf) - wr_stream->avail_out;
		ret = write_in_full(fd, zbuf, zlen);
		if (ret == -1)
			return -1;
		written += ret;
	}

	proto_ztrace(len, written, OUT);
	if (flush != Z_SYNC_FLUSH)
		die("no Z_SYNC_FLUSH");
	return written;
}

enum {
	WR_NOFLUSH,
	WR_FLUSH
};

static ssize_t cvs_write(struct cvs_transport *cvs, int flush, const char *fmt, ...) __attribute__((format (printf, 3, 4)));
static ssize_t cvs_write(struct cvs_transport *cvs, int flush, const char *fmt, ...)
{
	va_list args;
	ssize_t written;

	if (fmt) {
		va_start(args, fmt);
		strbuf_vaddf(&cvs->wr_buf, fmt, args);
		va_end(args);
	}

	if (flush == WR_NOFLUSH)
		return 0;

	if (cvs->compress)
		written = z_write_in_full(cvs->fd[1], &cvs->wr_stream, cvs->wr_buf.buf, cvs->wr_buf.len);
	else
		written = write_in_full(cvs->fd[1], cvs->wr_buf.buf, cvs->wr_buf.len);

	if (written == -1)
		return -1;

	proto_trace(cvs->wr_buf.buf, cvs->compress ? cvs->wr_buf.len : written, OUT);
	strbuf_reset(&cvs->wr_buf);

	cvs->written += written;
	cvs_written_total += written;
	return 0;
}

static ssize_t cvs_write_full(struct cvs_transport *cvs, const char *buf, size_t len)
{
	ssize_t written;

	if (cvs->wr_buf.len &&
	    cvs_write(cvs, WR_FLUSH, NULL))
		return -1;

	if (cvs->compress)
		written = z_write_in_full(cvs->fd[1], &cvs->wr_stream, buf, len);
	else
		written = write_in_full(cvs->fd[1], buf, len);

	if (written == -1)
		return -1;

	proto_trace(cvs->wr_buf.buf, cvs->compress ? len : written, OUT_BLOB);
	strbuf_reset(&cvs->wr_buf);

	cvs->written += written;
	cvs_written_total += written;
	return 0;
}

static ssize_t z_xread(int fd, git_zstream *rd_stream, void *zbuf, size_t zbuf_len,
		       void *buf, size_t buf_len)
{
	ssize_t zreadn;
	ssize_t readn;
	int ret;

	if (!rd_stream->next_in) {
		rd_stream->next_in = zbuf;
		rd_stream->avail_in = 0;
	}

	rd_stream->next_out = buf;
	rd_stream->avail_out = buf_len;
	zreadn = rd_stream->avail_in;

	do {
		if (!rd_stream->avail_in) {
			zreadn = xread(fd, zbuf, zbuf_len);
			if (zreadn <= 0)
				return zreadn;
			rd_stream->next_in = zbuf;
			rd_stream->avail_in = zreadn;
		}

		ret = git_inflate(rd_stream, 0);
		if (ret != Z_OK && ret != Z_STREAM_END)
			die("inflate failed");

		zreadn -= rd_stream->avail_in;
		readn = buf_len - rd_stream->avail_out;
		proto_ztrace(readn, zreadn, IN);
	} while(!readn || ret);

	return readn;
}

static ssize_t z_read_in_full(int fd, git_zstream *rd_stream, void *zbuf, size_t zbuf_len,
		       void *buf, size_t count)
{
	char *p = buf;
	ssize_t total = 0;

	while (count > 0) {
		ssize_t loaded = z_xread(fd, rd_stream, zbuf, zbuf_len, p, count);
		if (loaded < 0)
			return -1;
		if (loaded == 0)
			return total;
		count -= loaded;
		p += loaded;
		total += loaded;
	}

	return total;
}

static ssize_t cvs_readline(struct cvs_transport *cvs, struct strbuf *sb)
{
	char *newline;
	ssize_t readn;
	size_t linelen;

	strbuf_reset(sb);

	while (1) {
		newline = memchr(cvs->rd_buf.buf, '\n', cvs->rd_buf.len);
		if (newline) {
			linelen = newline - cvs->rd_buf.buf;
			strbuf_add(sb, cvs->rd_buf.buf, linelen);

			if (trace_want(trace_key)) {
				sb->buf[sb->len] = '\n';
				proto_trace(sb->buf, sb->len + 1, IN);
				sb->buf[sb->len] = '\0';
			}
			cvs->read += sb->len + 1;
			cvs_read_total += sb->len + 1;

			cvs->rd_buf.buf += linelen + 1;
			cvs->rd_buf.len -= linelen + 1;
			/*
			 * FIXME: returns length with '\n'
			 */
			return sb->len + 1;
		}

		if (cvs->rd_buf.len) {
			strbuf_add(sb, cvs->rd_buf.buf, cvs->rd_buf.len);
			cvs->rd_buf.len = 0;
		}
		cvs->rd_buf.buf = cvs->rd_buf.data;

		if (cvs->compress)
			readn = z_xread(cvs->fd[0], &cvs->rd_stream,
					cvs->rd_zbuf, sizeof(cvs->rd_zbuf),
					cvs->rd_buf.buf, sizeof(cvs->rd_buf.data));
		else
			readn = xread(cvs->fd[0], cvs->rd_buf.buf, sizeof(cvs->rd_buf.data));

		if (readn <= 0) {
			proto_trace(NULL, 0, IN);
			return -1;
		}

		cvs->rd_buf.len = readn;
	}

	return -1;
}

static ssize_t _cvs_read_full_from_buf(struct cvs_transport *cvs, char *buf, ssize_t size)
{
	size_t readn;

	readn = cvs->rd_buf.len < size ? cvs->rd_buf.len : size;

	memcpy(buf, cvs->rd_buf.buf, readn);

	cvs->rd_buf.buf += readn;
	cvs->rd_buf.len -= readn;
	if (!cvs->rd_buf.len) {
		cvs->rd_buf.buf = cvs->rd_buf.data;
		cvs->rd_buf.len = 0;
	}

	return readn;
}

static ssize_t cvs_read_full(struct cvs_transport *cvs, char *buf, ssize_t size)
{
	ssize_t readn = 0;
	ssize_t ret;
	char *pbuf = buf;

	if (cvs->rd_buf.len) {
		readn = _cvs_read_full_from_buf(cvs, buf, size);

		pbuf += readn;
		size -= readn;
	}

	if (cvs->compress)
		ret = z_read_in_full(cvs->fd[0], &cvs->rd_stream,
				cvs->rd_zbuf, sizeof(cvs->rd_zbuf),
				pbuf, size);
	else
		ret = read_in_full(cvs->fd[0], pbuf, size);

	if (ret == -1)
		die("read full failed");

	readn += ret;
	proto_trace(buf, readn, IN_BLOB);
	cvs->read += readn;
	cvs_read_total += readn;
	return readn;
}

static ssize_t z_finish_write(int fd, git_zstream *wr_stream)
{
	unsigned char zbuf[ZBUF_SIZE];
	unsigned long zlen;
	ssize_t written = 0;

	wr_stream->next_in = (void *)NULL;
	wr_stream->avail_in = 0;

	wr_stream->next_out = zbuf;
	wr_stream->avail_out = sizeof(zbuf);

	if (git_deflate(wr_stream, Z_FINISH) != Z_STREAM_END)
		die("deflate finish failed");

	zlen = sizeof(zbuf) - wr_stream->avail_out;
	written = write_in_full(fd, zbuf, zlen);
	if (written == -1)
		return -1;

	proto_ztrace(0, written, OUT);
	return written;
}

static void z_terminate_gently(struct cvs_transport *cvs)
{
	ssize_t readn;

	z_finish_write(cvs->fd[1], &cvs->wr_stream);
	do {
		readn = z_xread(cvs->fd[0], &cvs->rd_stream,
				cvs->rd_zbuf, sizeof(cvs->rd_zbuf),
				cvs->rd_buf.buf, sizeof(cvs->rd_buf.data));
		proto_trace(cvs->rd_buf.buf, readn, IN);
	} while(readn);
}

static int strbuf_gettext_after(struct strbuf *sb, const char *what, struct strbuf *out)
{
	size_t len = strlen(what);
	if (!strncmp(sb->buf, what, len)) {
		strbuf_copybuf(out, sb->buf + len, sb->len - len);
		return 1;
	}
	return 0;
}

static int strbuf_startswith(struct strbuf *sb, const char *what)
{
	return !strncmp(sb->buf, what, strlen(what));
}

static int strbuf_endswith(struct strbuf *sb, const char *what)
{
	size_t len = strlen(what);
	if (sb->len < len)
		return 0;

	return !strcmp(sb->buf + sb->len - len, what);
}

static int cvs_getreply(struct cvs_transport *cvs, struct strbuf *sb, const char *reply)
{
	int found = 0;
	ssize_t ret;

	while (1) {
		ret = cvs_readline(cvs, &cvs->rd_line_buf);
		if (ret <= 0)
			return -1;

		if (strbuf_startswith(sb, "E "))
			tracef("CVS E: %s", sb->buf + 2);

		if (strbuf_gettext_after(&cvs->rd_line_buf, reply, sb))
			found = 1;

		if (!strcmp(cvs->rd_line_buf.buf, "ok"))
			break;

		if (strbuf_startswith(&cvs->rd_line_buf, "error")) {
			tracef("CVS Error: %s", cvs->rd_line_buf.buf);
			return -1;
		}
	}

	return !found;
}

static int cvs_getreply_firstmatch(struct cvs_transport *cvs, struct strbuf *sb, const char *reply)
{
	ssize_t ret;

	while (1) {
		ret = cvs_readline(cvs, &cvs->rd_line_buf);
		if (ret <= 0)
			return -1;

		if (strbuf_startswith(&cvs->rd_line_buf, "E "))
			tracef("CVS E: %s", cvs->rd_line_buf.buf + 2);

		if (strbuf_gettext_after(&cvs->rd_line_buf, reply, sb))
			return 0;

		if (!strcmp(cvs->rd_line_buf.buf, "ok"))
			return 1;

		if (strbuf_startswith(&cvs->rd_line_buf, "error")) {
			tracef("CVS Error: %s", cvs->rd_line_buf.buf);
			return -1;
		}
	}

	return -1;
}

static int cvs_init_compress(struct cvs_transport *cvs, int compress)
{
	if (!compress)
		return 0;

	if (cvs_write(cvs, WR_FLUSH, "Gzip-stream %d\n", compress) == -1)
		die("cvs_write failed");
	cvs->compress = compress;

	git_deflate_init(&cvs->wr_stream, compress);
	git_inflate_init(&cvs->rd_stream);

	return 0;
}

static int cvs_negotiate(struct cvs_transport *cvs)
{
	static const char *used_capabilities[] = {
		"add",
		"ci",
		"co",
		"rlog",
		"status",
		"UseUnchanged",
		NULL
	};
	const char **caps = used_capabilities;
	int no_used_caps = 0;
	int has_version_support;
	int has_gzip_support;
	struct strbuf reply = STRBUF_INIT;
	struct string_list cvs_capabilities = STRING_LIST_INIT_NODUP;
	ssize_t ret;

	ret = cvs_write(cvs,
			WR_FLUSH,
			"Root %s\n"
			"Valid-responses ok error Valid-requests Checked-in New-entry Checksum Copy-file Updated Created Merged Patched Rcs-diff Mode Mod-time Removed Remove-entry Set-static-directory Clear-static-directory Set-sticky Clear-sticky Template Notified Module-expansion Wrapper-rcsOption M E\n"
			"valid-requests\n",
			cvs->repo_path);

	if (ret == -1)
		die("failed to connect");

	ret = cvs_getreply(cvs, &reply, "Valid-requests ");
	if (ret)
		return -1;

	//tracef("CVS Valid-requests: %s", reply.buf);

	string_list_split_in_place(&cvs_capabilities, reply.buf, ' ', -1);
	sort_string_list(&cvs_capabilities);
	while (*caps) {
		if (!string_list_has_string(&cvs_capabilities, *caps)) {
			error("required request: %s is not support by CVS server", *caps);
			no_used_caps = 1;
		}
		caps++;
	}

	has_version_support = string_list_has_string(&cvs_capabilities, "version");
	if (!has_version_support)
		warning("CVS server does not support version request");

	has_gzip_support = string_list_has_string(&cvs_capabilities, "Gzip-stream");
	if (!has_gzip_support)
		warning("CVS server does not support gzip compression");

	cvs->has_rls_support = string_list_has_string(&cvs_capabilities, "rlist");
	if (!cvs->has_rls_support)
		tracef("CVS server does not support rls request (checkout will be used instead)");
	//else
	//	tracef("CVS server support rls request");
	string_list_clear(&cvs_capabilities, 0);

	cvs->has_rlog_S_option = !dumb_rlog;
	if (getenv("GIT_CVS_DUMB_RLOG"))
		cvs->has_rlog_S_option = 0;

	cvs_write(cvs, WR_NOFLUSH, "UseUnchanged\n");

	if (has_gzip_support) {
		const char *gzip = getenv("GZIP");
		if (gzip)
			cvs_init_compress(cvs, atoi(gzip));
		else
			cvs_init_compress(cvs, 1);
	}

	if (has_version_support) {
		ret = cvs_write(cvs, WR_FLUSH, "version\n");
		if (ret)
			die("cvs_write failed");

		ret = cvs_getreply(cvs, &reply, "M ");
		if (ret)
			return -1;

		//tracef("CVS Server version: %s", reply.buf);
		if (!dumb_rlog && strstr(reply.buf, "1.11.1p1")) {
			cvs->has_rlog_S_option = 0;
			warning("CVS server does not support rlog -S option");
		}
	}

	if (!cvs->has_rlog_S_option)
		warning("using dumb rlog with no -S option support (delta updates will take longer)");

	strbuf_release(&reply);
	if (no_used_caps)
		return -1;
	return 0;
}

static unsigned char cvs_scramble_shifts[] = {
	  0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
	 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
	114,120, 53, 79, 96,109, 72,108, 70, 64, 76, 67,116, 74, 68, 87,
	111, 52, 75,119, 49, 34, 82, 81, 95, 65,112, 86,118,110,122,105,
	 41, 57, 83, 43, 46,102, 40, 89, 38,103, 45, 50, 42,123, 91, 35,
	125, 55, 54, 66,124,126, 59, 47, 92, 71,115, 78, 88,107,106, 56,
	 36,121,117,104,101,100, 69, 73, 99, 63, 94, 93, 39, 37, 61, 48,
	 58,113, 32, 90, 44, 98, 60, 51, 33, 97, 62, 77, 84, 80, 85,223,
	225,216,187,166,229,189,222,188,141,249,148,200,184,136,248,190,
	199,170,181,204,138,232,218,183,255,234,220,247,213,203,226,193,
	174,172,228,252,217,201,131,230,197,211,145,238,161,179,160,212,
	207,221,254,173,202,146,224,151,140,196,205,130,135,133,143,246,
	192,159,244,239,185,168,215,144,139,165,180,157,147,186,214,176,
	227,231,219,169,175,156,206,198,129,164,150,210,154,177,134,127,
	182,128,158,208,162,132,167,209,149,241,153,251,237,236,171,195,
	243,233,253,240,194,250,191,155,142,137,245,235,163,242,178,152
};

char *cvs_scramble(const char *password)
{
	char *scrambled;
	unsigned char *p;

	scrambled = xcalloc(1, strlen(password) + 2);
	scrambled[0] = 'A';
	strcpy(scrambled + 1, password);
	p = (unsigned char *)scrambled + 1;

	while (*p) {
		*p = cvs_scramble_shifts[*p];
		p++;
	}

	return scrambled;
}

static int cvs_pserver_login(struct cvs_transport *cvs)
{
	struct strbuf reply = STRBUF_INIT;
	static char *empty_pass = "A";
	char *scrambled_pass = empty_pass;
	ssize_t ret;

	if (!cvs->username)
		die("not cvs user set for pserver connection");

	if (cvs->password)
		scrambled_pass = cvs_scramble(cvs->password);

	ret = cvs_write(cvs,
			WR_FLUSH,
			"BEGIN AUTH REQUEST\n"
			"%s\n"
			"%s\n"
			"%s\n"
			"END AUTH REQUEST\n",
			cvs->repo_path,
			cvs->username,
			scrambled_pass);

	if (scrambled_pass != empty_pass)
		free(scrambled_pass);

	if (ret == -1)
		die("Cannot send cvs auth request");

	ret = cvs_readline(cvs, &reply);
	if (ret <= 0)
		return -1;

	if (!strcmp(reply.buf, "I LOVE YOU"))
		return 0;

	if (!strcmp(reply.buf, "I HATE YOU"))
		die("cvs server authorization failed for user: %s", cvs->username);

	die("cvs server authorization failed: %s", reply.buf);
}

static void strbuf_complete_line_ch(struct strbuf *sb, char ch)
{
	if (sb->len && sb->buf[sb->len - 1] != ch)
		strbuf_addch(sb, ch);
}

static void strbuf_rtrim_ch(struct strbuf *sb, char ch)
{
	if (sb->len > 0 && sb->buf[sb->len - 1] == ch)
		sb->len--;
	sb->buf[sb->len] = '\0';
}

struct cvs_transport *cvs_connect(const char *cvsroot, const char *module)
{
	struct cvs_transport *cvs;
	struct strbuf sb = STRBUF_INIT;

#ifdef DB_CACHE
	db_cache_init_default();
#endif

	cvs = xcalloc(1, sizeof(*cvs));
	cvs->rd_buf.buf = cvs->rd_buf.data;
	strbuf_init(&cvs->rd_line_buf, 0);
	strbuf_init(&cvs->wr_buf, 0);
	if (parse_cvsroot(cvs, cvsroot))
		die(_("Malformed cvs root format."));
	strbuf_copystr(&sb, module);
	strbuf_rtrim_ch(&sb, '/');
	cvs->module = strbuf_detach(&sb, NULL);

	strbuf_copystr(&sb, cvs->repo_path);
	strbuf_complete_line_ch(&sb, '/');
	if (cvs->module[0] == '/')
		die("CVS module name should not start with '/'");

	strbuf_addstr(&sb, cvs->module);
	strbuf_complete_line_ch(&sb, '/');

	cvs->full_module_path = strbuf_detach(&sb, NULL);

	switch (cvs->protocol) {
	case cvs_proto_pserver:
	case cvs_proto_ext:
	case cvs_proto_local:
		cvs->conn = cvs_init_transport(cvs, "cvs server", CONNECT_VERBOSE);
		if (!cvs->conn) {
			free(cvs);
			return NULL;
		}
		break;
	default:
		die(_("Unsupported cvs connection type."));
	}

	if (cvs->protocol == cvs_proto_pserver &&
	    cvs_pserver_login(cvs)) {
		cvs_terminate(cvs);
		return NULL;
	}

	if (cvs_negotiate(cvs)) {
		error("CVS protocol negotiation failed.");
		cvs_terminate(cvs);
		return NULL;
	}

	strbuf_release(&sb);
	return cvs;
}

int cvs_terminate(struct cvs_transport *cvs)
{
	int rc = 0;
	struct child_process *conn = cvs->conn;

	if (cvs->compress) {
		z_terminate_gently(cvs);
		git_deflate_end_gently(&cvs->wr_stream);
		git_inflate_end(&cvs->rd_stream);
	}

	close(cvs->fd[1]);
	close(cvs->fd[0]);
	strbuf_release(&cvs->rd_line_buf);
	strbuf_release(&cvs->wr_buf);

	if (cvs->host)
		free(cvs->host);
	if (cvs->username)
		free(cvs->username);
	if (cvs->password)
		free(cvs->password);

	if (cvs->repo_path)
		free(cvs->repo_path);
	if (cvs->module)
		free(cvs->module);
	if (cvs->full_module_path)
		free(cvs->full_module_path);
	free(cvs);

	if (conn != &no_fork)
		rc = finish_connect(conn);
	return rc;
}

char **cvs_gettags(struct cvs_transport *cvs)
{
	char **tags;
	tags = xcalloc(16, sizeof(*tags));

	return tags;
}

struct branch_rev {
	struct strbuf name;
	struct strbuf rev;
};

struct branch_rev_list {
	unsigned int size, nr;
	struct branch_rev *array;
};

#define for_each_branch_rev_list_item(item,list) \
	for (item = (list)->array; item < (list)->array + (list)->nr; ++item)

void branch_rev_list_init(struct branch_rev_list *list)
{
	list->size = 0;
	list->nr = 0;
	list->array = NULL;
}

static void rev_list_grow(struct branch_rev_list *list, unsigned int nr)
{
	if (nr > list->size) {
		unsigned int was = list->size;
		struct branch_rev *it;
		if (alloc_nr(list->size) < nr)
			list->size = nr;
		else
			list->size = alloc_nr(list->size);
		list->array = xrealloc(list->array, list->size * sizeof(*list->array));
		for (it = list->array + was;
		     it < list->array + list->size;
		     it++) {
			strbuf_init(&it->name, 0);
			strbuf_init(&it->rev, 0);
		}
	}
}

void branch_rev_list_push(struct branch_rev_list *list, struct strbuf *name, struct strbuf *rev)
{
	rev_list_grow(list, list->nr + 1);

	strbuf_swap(&list->array[list->nr].name, name);
	strbuf_swap(&list->array[list->nr].rev, rev);
	++list->nr;
}

int branch_rev_list_find(struct branch_rev_list *list, struct strbuf *rev, struct strbuf *name)
{
	struct branch_rev *item;

	for_each_branch_rev_list_item(item, list)
		if (!strbuf_cmp(&item->rev, rev)) {
			strbuf_copybuf(name, item->name.buf, item->name.len);
			return 1;
		}

	return 0;
}

void branch_rev_list_clear(struct branch_rev_list *list)
{
	list->nr = 0;
}

void branch_rev_list_release(struct branch_rev_list *list)
{
	struct branch_rev *item;

	if (!list->array)
		return;

	for_each_branch_rev_list_item(item, list) {
		strbuf_release(&item->name);
		strbuf_release(&item->rev);
	}

	free(list->array);
	branch_rev_list_init(list);
}

int strip_last_rev_num(struct strbuf *branch_rev)
{
	char *idx;
	int num;

	idx = strrchr(branch_rev->buf, '.');
	if (!idx)
		return -1;

	num = atoi(idx+1);
	strbuf_setlen(branch_rev, idx - branch_rev->buf);

	return num;
}

enum {
	sym_invalid = 0,
	sym_branch,
	//sym_vendor_branch,
	sym_tag
};

/*
 * branch revision cases:
 * x.y.z   - vendor branch if odd number of numbers (even number of dots)
 * x.y.0.z - branch, has magic branch number 0, normalized to x.y.z
 * x.y     - tag, no magic branch number
 */
int parse_branch_rev(struct strbuf *branch_rev)
{
	char *dot;
	char *last_dot = NULL;
	char *prev_dot = NULL;
	int prev_num;
	int dots = 0;

	dot = branch_rev->buf;

	while (1) {
		dot = strchr(dot, '.');
		if (!dot)
			break;

		dots++;
		prev_dot = last_dot;
		last_dot = dot;
		dot++;
	}

	/*while (*dot) {
		if (*dot == '.') {
			dots++;
			prev_dot = last_dot;
			last_dot = dot;
		}
		dot++;
	}*/

	if (prev_dot) {
		if (!(dots % 2))
			return sym_branch; //sym_vendor_branch;

		prev_num = atoi(prev_dot + 1);
		if (!prev_num) {
			strbuf_remove(branch_rev, prev_dot - branch_rev->buf, last_dot - prev_dot);
			return sym_branch;
		}
		return sym_tag;
	}

	if (!last_dot)
		die("Cannot parse branch revision");
	return last_dot ? sym_tag : sym_invalid;
}

int parse_sym(struct strbuf *reply, struct strbuf *branch_name, struct strbuf *branch_rev)
{
	char *idx;

	idx = strchr(reply->buf, ':');
	if (!idx)
		return sym_invalid;

	strbuf_copybuf(branch_name, reply->buf, idx - reply->buf);

	++idx;
	if (isspace(*idx))
		++idx;

	strbuf_copystr(branch_rev, idx);

	return parse_branch_rev(branch_rev);
}

//int parse_sym(struct strbuf *reply, struct strbuf *branch_name, struct strbuf *branch_rev)
//{
//	char *idx;
//	int branch_num;
//	int rev_num;
//
//	idx = strchr(reply->buf, ':');
//	if (!idx)
//		return -1;
//
//	strbuf_add(branch_name, reply->buf, idx - reply->buf);
//
//	++idx;
//	if (isspace(*idx))
//		++idx;
//
//	strbuf_addstr(branch_rev, idx);
//
//	branch_num = strip_last_rev_num(branch_rev);
//	if (branch_rev <= 0)
//		die("Cannot parse CVS branch revision");
//
//	rev_num = strip_last_rev_num(branch_rev);
//	if (rev_num == -1) {
//		/*
//		 * FIXME: handle tags like: 1.5
//		 */
//		//error("Skipping CVS branch tag");
//		return -1;
//	}
//
//	if (rev_num == 0) {
//		strbuf_addf(branch_rev, ".%d", branch_num);
//		return 0;
//	}
//
//	/*
//	 * FIXME: handle vendor branches: 1.1.1
//	 * FIXME: handle tags like: 1.5.1.3
//	 */
//	//error("Skipping CVS branch tag or Vendor branch");
//	return -1;
//}

void trim_revision(struct strbuf *revision)
{
	char *p;

	p = revision->buf;
	while (*p && (isdigit(*p) || *p == '.'))
		p++;

	if (*p)
		strbuf_setlen(revision, p - revision->buf);
}

int is_revision_metadata(struct strbuf *reply)
{
	char *p1, *p2;

	if (!(p1 = strchr(reply->buf, ':')))
		return 0;

	p2 = strchr(reply->buf, ' ');

	if (p2 && p2 < p1)
		return 0;

	if (!strbuf_endswith(reply, ";"))
		return 0;

	return 1;
}

time_t date_to_unixtime(const char *date)
{
	struct tm date_tm;
	char *p;

	memset(&date_tm, 0, sizeof(date_tm));
	p = strptime(date, "%Y/%m/%d %T", &date_tm);
	if (!p) {
		// try: 2013-01-18 13:28:28 +0000
		p = strptime(date, "%Y-%m-%d %T", &date_tm);
		if (!p)
			return 0;
	}

	setenv("TZ", "UTC", 1);
	tzset();

	return mktime(&date_tm);
}

time_t rfc2822_date_to_unixtime(const char *date)
{
	struct tm date_tm;
	char *p;

	memset(&date_tm, 0, sizeof(date_tm));
	p = strptime(date, "%d %b %Y %T %z", &date_tm);
	if (!p)
		return 0;

	setenv("TZ", "UTC", 1);
	tzset();

	return mktime(&date_tm);
}

time_t entry_date_to_unixtime(const char *date)
{
	struct tm date_tm;
	char *p;

	memset(&date_tm, 0, sizeof(date_tm));
	// Sun Mar 17 15:57:38 2013
	p = strptime(date, "%a %b %d %T %Y", &date_tm);
	if (!p)
		return 0;

	setenv("TZ", "UTC", 1);
	tzset();

	return mktime(&date_tm);
}

static unsigned int hash_str(const char *branch)
{
	unsigned int hash = 0x12375903;

	while (*branch) {
		unsigned char c = *branch++;
		hash = hash*101 + c;
	}
	return hash;
}

static void add_branch_hash(struct hash_table *branch_hash, const char *branch_name)
{
	const char *old;
	unsigned int hash;

	hash = hash_str(branch_name);
	old = lookup_hash(hash, branch_hash);
	if (old) {
		if (strcmp(old, branch_name))
			die("branch name hash collision %s %s", old, branch_name);
	}
	else {
		insert_hash(hash, xstrdup(branch_name), branch_hash);
	}
}

static int add_to_string_list(void *ptr, void *data)
{
	char *branch_name = ptr;
	struct string_list *list = data;

	if (!unsorted_string_list_lookup(list, branch_name))
		string_list_append_nodup(list, branch_name);
	else
		free(branch_name);
	return 0;
}

#define CVS_LOG_BOUNDARY "----------------------------"
#define CVS_FILE_BOUNDARY "============================================================================="

enum
{
	NEED_RCS_FILE		= 0,
	NEED_WORKING_FILE	= 1,
	NEED_SYMS		= 2,
	NEED_EOS		= 3,
	NEED_START_LOG		= 4,
	NEED_REVISION		= 5,
	NEED_DATE_AUTHOR_STATE	= 6,
	NEED_EOM		= 7,
	SKIP_LINES		= 8
};

static int parse_cvs_rlog(struct cvs_transport *cvs, struct string_list *branch_lst,
		  struct string_list *tag_lst, add_rev_fn_t cb, void *data)
{
	struct strbuf reply = STRBUF_INIT;
	ssize_t ret;

	struct strbuf file = STRBUF_INIT;
	struct strbuf revision = STRBUF_INIT;
	struct strbuf branch = STRBUF_INIT;
	struct strbuf author = STRBUF_INIT;
	struct strbuf message = STRBUF_INIT;
	time_t timestamp = 0;
	int is_dead = 0;

	int branches_max = 0;
	int branches = 0;
	int tags_max = 0;
	int tags = 0;
	int files = 0;
	int revs = 0;

	int state = NEED_RCS_FILE;
	int have_log = 0;
	int skip_unknown = 0;

	/*
	 * branch revision -> branch name, hash created per file
	 */
	struct hash_table branch_hash = HASH_TABLE_INIT;
	struct hash_table tag_hash = HASH_TABLE_INIT;
	struct strbuf branch_name = STRBUF_INIT;
	struct strbuf branch_rev = STRBUF_INIT;

	struct branch_rev_list branch_list;
	branch_rev_list_init(&branch_list);

	size_t len;
	int read_rlog = 0;
	int write_rlog = 0;
	FILE *rlog = NULL;
	const char *rlog_path = getenv("GIT_CACHE_CVS_RLOG");
	if (rlog_path) {
		if (!access(rlog_path, R_OK)) {
			read_rlog = 1;
			rlog = fopen(rlog_path, "r");
			if (!rlog)
				die("cannot open %s for reading", rlog_path);
		}
		else {
			write_rlog = 1;
			rlog = fopen(rlog_path, "w");
			if (!rlog)
				die("cannot open %s for writing", rlog_path);
		}
	}
	//free(cvs->full_module_path);
	//cvs->full_module_path = xstrdup("/cvs/se/cvs/all/se/");
	//cvs->full_module_path = xstrdup("/cvs/zfsp/cvs/");
	//cvs->full_module_path = xstrdup("/cvs/zfsp/cvs/scsn");
	strbuf_grow(&reply, CVS_MAX_LINE);

	while (1) {
		if (read_rlog) {
			if (!fgets(reply.buf, reply.alloc, rlog))
				break;

			len = strlen(reply.buf);
			cvs_read_total += len;
			strbuf_setlen(&reply, len);
			if (len && reply.buf[len - 1] == '\n')
				strbuf_setlen(&reply, len - 1);
		}
		else {
			ret = cvs_getreply_firstmatch(cvs, &reply, "M ");
			if (ret == -1)
				return -1;
			else if (ret == 1) /* ok from server */
				break;

			if (write_rlog)
				fprintf(rlog, "%s\n", reply.buf);
		}

		switch(state) {
		case NEED_RCS_FILE:
			if (strbuf_gettext_after(&reply, "RCS file: ", &file)) {
				branch_rev_list_clear(&branch_list);
				files++;
				branches = 0;
				tags = 0;

				if (strbuf_startswith(&file, cvs->full_module_path)) {
					char *attic;

					if (!strbuf_endswith(&file, ",v"))
						die("RCS file name does not end with ,v");
					strbuf_setlen(&file, file.len - 2);

					attic = strstr(file.buf, "/Attic/");
					if (attic)
						strbuf_remove(&file, attic - file.buf, strlen("/Attic"));

					strbuf_remove(&file, 0, strlen(cvs->full_module_path));

					state = NEED_SYMS;
				}
				else {
					state = NEED_WORKING_FILE;
				}
			}
			break;
		case NEED_WORKING_FILE:
			if (strbuf_gettext_after(&reply, "Working file: ", &file)) {
				die("Working file: %s", file.buf);
				state = NEED_SYMS;
			}
			else {
				state = NEED_RCS_FILE;
			}
			break;
		case NEED_SYMS:
			if (strbuf_startswith(&reply, "symbolic names:"))
				state = NEED_EOS;
			break;
		case NEED_EOS:
			if (!isspace(reply.buf[0])) {
				/* see cvsps_types.h for commentary on have_branches */
				//file->have_branches = 1;
				state = NEED_START_LOG;
			}
			else {
				strbuf_ltrim(&reply);

				switch (parse_sym(&reply, &branch_name, &branch_rev)) {
				case sym_branch:
					branches++;
					if (branch_lst)
						add_branch_hash(&branch_hash, branch_name.buf);
					branch_rev_list_push(&branch_list, &branch_name, &branch_rev);
					break;
				case sym_tag:
					tags++;
					if (tag_lst)
						add_branch_hash(&tag_hash, branch_name.buf);
					break;
				}
			}
			break;
		case NEED_START_LOG:
			if (!strcmp(reply.buf, CVS_LOG_BOUNDARY))
				state = NEED_REVISION;
			else if (!strcmp(reply.buf, CVS_FILE_BOUNDARY))
				state = NEED_RCS_FILE;
			break;
		case NEED_REVISION:
			if (strbuf_gettext_after(&reply, "revision ", &revision)) {
				int num;

				revs++;

				strbuf_reset(&branch);
				strbuf_reset(&author);
				strbuf_reset(&message);
				timestamp = 0;
				is_dead = 0;
				/* The "revision" log line can include extra information 
				 * including who is locking the file --- strip that out.
				 */
				trim_revision(&revision);

				strbuf_add(&branch, revision.buf, revision.len);
				num = strip_last_rev_num(&branch);
				if (num == -1)
					die("Cannot parse revision: %s", revision.buf);

				if (!strchr(branch.buf, '.')) {
					strbuf_copystr(&branch, "HEAD");
				}
				else {
					if (!branch_rev_list_find(&branch_list, &branch, &branch)) {
						error("Cannot find branch for: %s rev: %s branch: %s",
						      file.buf, revision.buf, branch.buf);
						strbuf_copystr(&branch, "UNKNOWN");
						skip_unknown = 1;
					}
				}

				state = NEED_DATE_AUTHOR_STATE;

				/*
				 * FIXME: cvsps extra case in which state = NEED_EOM;
				 */
			}
			break;
		case NEED_DATE_AUTHOR_STATE:
			if (strbuf_startswith(&reply, "date: ")) {
				struct strbuf **tokens, **it;

				tokens = strbuf_split_max(&reply, ';', 4);
				it = tokens;

				strbuf_trim(*it);
				if (!strbuf_gettext_after(*it, "date: ", &reply))
					die("Cannot parse CVS rlog: date");
				strbuf_rtrim_ch(&reply, ';');

				timestamp = date_to_unixtime(reply.buf);
				if (!timestamp)
					die("Cannot parse CVS rlog date: %s", reply.buf);

				/*
				 * FIXME: is following data optional?
				 */
				it++;
				strbuf_trim(*it);
				if (!strbuf_gettext_after(*it, "author: ", &author))
					die("Cannot parse CVS rlog: author");
				strbuf_rtrim_ch(&author, ';');

				it++;
				strbuf_trim(*it);
				if (!strbuf_gettext_after(*it, "state: ", &reply))
					die("Cannot parse CVS rlog: state");
				strbuf_rtrim_ch(&reply, ';');

				if (!strcmp(reply.buf, "dead"))
					is_dead = 1;

				strbuf_list_free(tokens);

				state = NEED_EOM;
				have_log = 0;
			}
			break;
		case NEED_EOM:
			if (!strcmp(reply.buf, CVS_LOG_BOUNDARY))
				state = NEED_REVISION;
			else if (!strcmp(reply.buf, CVS_FILE_BOUNDARY))
				state = NEED_RCS_FILE;
			else if (have_log || !is_revision_metadata(&reply)) {
					have_log = 1;
					strbuf_add(&message, reply.buf, reply.len);
					strbuf_addch(&message, '\n');
			}

			if (state != NEED_EOM) {
				//tracef("BRANCH: %s\nREV: %s %s %s %d %lu\nMSG: %s--", branch.buf,
				//	file.buf, revision.buf, author.buf, is_dead, timestamp, message.buf);
				if (branches_max < branches)
					branches_max = branches;
				if (tags_max < tags)
					tags_max = tags;
				if (is_dead &&
				    !prefixcmp(message.buf, "file ") &&
				    (strstr(message.buf, "was initially added on branch") ||
				     strstr(message.buf, "was added on branch"))) {
					//tracef("skipping initial add to another branch file: %s rev: %s", file.buf, revision.buf);
				}
				else if (!skip_unknown)
					cb(branch.buf, file.buf, revision.buf, author.buf, message.buf, timestamp, is_dead, data);
				skip_unknown = 0;
			}
			break;
		}
	}

	if (rlog)
		fclose(rlog);

	if (state != NEED_RCS_FILE)
		die("Cannot parse rlog, parser state %d", state);

	if (branch_lst)
		for_each_hash(&branch_hash, add_to_string_list, branch_lst);
	if (tag_lst)
		for_each_hash(&tag_hash, add_to_string_list, tag_lst);

	tracef("REVS: %d FILES: %d BRANCHES: %d TAGS: %d", revs, files, branches_max, tags_max);

	strbuf_release(&branch_name);
	strbuf_release(&branch_rev);
	branch_rev_list_release(&branch_list);
	strbuf_release(&reply);
	strbuf_release(&file);
	strbuf_release(&revision);
	strbuf_release(&branch);
	strbuf_release(&author);
	strbuf_release(&message);
	free_hash(&branch_hash);
	free_hash(&tag_hash);
	return 0;
}

int cvs_rlog(struct cvs_transport *cvs, time_t since, time_t until,
		struct string_list *branch_lst, struct string_list *tag_lst,
		add_rev_fn_t cb, void *data)
{
	ssize_t ret;
	const char *rlog_path = getenv("GIT_CACHE_CVS_RLOG");
	if (rlog_path && !access(rlog_path, R_OK))
		return parse_cvs_rlog(cvs, branch_lst, tag_lst, cb, data);

	if (since) {
		cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -d\n"
			"Argument %s<1 Jan 2038 05:00:00 -0000\n",
			show_date(since, 0, DATE_RFC2822));
	}

	if (cvs->has_rlog_S_option)
		cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -S\n");

	ret = cvs_write(cvs,
			WR_FLUSH,
			"Argument --\n"
			"Argument %s\n"
			"rlog\n",
			cvs->module);

	if (ret == -1)
		die("Cannot send rlog command");

	return parse_cvs_rlog(cvs, branch_lst, tag_lst, cb, data);
}

/*
mod/src/docs:
/Makefile.am/1.1/Sat Apr 27 18:27:51 2013/-kk/
/hooks.sgml/1.1/Sat Apr 27 18:27:51 2013/-kk/
D/examples////
*/

enum {
	NEED_DIR = 1,
	NEED_FILES = 2
};

int parse_cvs_rls(struct cvs_transport *cvs, const char *rls_path, on_rev_fn_t cb, void *data)
{
	struct strbuf reply = STRBUF_INIT;
	ssize_t ret;

	struct strbuf file = STRBUF_INIT;
	struct strbuf revision = STRBUF_INIT;
	struct strbuf date = STRBUF_INIT;
	struct strbuf dir = STRBUF_INIT;
	time_t unix_timestamp;

	char *rev_start;
	char *rev_end;
	char *date_end;
	int state = NEED_DIR;

	strbuf_grow(&reply, CVS_MAX_LINE);

	int read_rls = 0;
	int write_rls = 0;
	FILE *rls = NULL;
	if (rls_path) {
		if (!access(rls_path, R_OK)) {
			read_rls = 1;
			rls = fopen(rls_path, "r");
			if (!rls)
				die("cannot open %s for reading", rls_path);
		}
		else {
			write_rls = 1;
			rls = fopen(rls_path, "w");
			if (!rls)
				die("cannot open %s for writing", rls_path);
		}
	}
	strbuf_grow(&reply, CVS_MAX_LINE);

	while (1) {
		if (read_rls) {
			if (!fgets(reply.buf, reply.alloc, rls))
				break;

			size_t len = strlen(reply.buf);
			strbuf_setlen(&reply, len);
			if (len && reply.buf[len - 1] == '\n')
				strbuf_setlen(&reply, len - 1);
		}
		else {
			ret = cvs_getreply_firstmatch(cvs, &reply, "M ");
			if (ret == -1)
				return -1;
			else if (ret == 1) /* ok from server */
				break;

			if (write_rls)
				fprintf(rls, "%s\n", reply.buf);
		}

		if (state == NEED_DIR) {
			if (!reply.len)
				continue;
			if (reply.buf[0] == '/' || suffixcmp(reply.buf, ":"))
				die("cvs rls parse failed: waiting for directory, got: %s", reply.buf);

			if (!strbuf_gettext_after(&reply, cvs->module, &dir) || !dir.len)
				die("cvs rls directory does not contain module path: %s", reply.buf);

			strbuf_setlen(&dir, dir.len - 1);
			if (dir.len) {
				strbuf_remove(&dir, 0, 1);
				strbuf_complete_line_ch(&dir, '/');
			}
			state = NEED_FILES;
		}
		else {
			if (!reply.len) {
				state = NEED_DIR;
				continue;
			}

			if (reply.buf[0] != '/')
				continue;

			unix_timestamp = 0;

			rev_start = strchr(reply.buf + 1, '/');
			if (!rev_start)
				die("malformed file entry: %s", reply.buf);
			*rev_start++ = '\0';

			rev_end = strchr(rev_start, '/');
			if (!rev_end)
				die("malformed rev entry: %s", rev_start);
			*rev_end = '\0';
			rev_end++;

			date_end = strchr(rev_end, '/');
			if (!date_end)
				die("malformed date entry: %s", rev_end);
			*date_end = '\0';

			strbuf_reset(&file);
			strbuf_addf(&file, "%s%s", dir.buf, reply.buf + 1);
			strbuf_copystr(&revision, rev_start);
			strbuf_copystr(&date, rev_end);
			unix_timestamp = entry_date_to_unixtime(date.buf);

			cb(file.buf, revision.buf, unix_timestamp, data);
		}
	}

	if (rls)
		fclose(rls);
	strbuf_release(&reply);
	strbuf_release(&file);
	strbuf_release(&revision);
	strbuf_release(&date);
	strbuf_release(&dir);
	return 0;
}

int cvs_rls(struct cvs_transport *cvs, const char *branch, int show_dead, time_t date, on_rev_fn_t cb, void *data)
{
	ssize_t ret;
	int rc;
	struct strbuf rls_path = STRBUF_INIT;
	const char *cache_dir = getenv("GIT_CACHE_CVS_DIR");
	if (cache_dir) {
		strbuf_addf(&rls_path, "%s/cvsrls.%s.%d.%ld", cache_dir, branch, show_dead, date);
		if (!access(rls_path.buf, R_OK)) {
			rc = parse_cvs_rls(cvs, rls_path.buf, cb, data);
			strbuf_release(&rls_path);
			return rc;
		}
	}

	cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -e\n"
			"Argument -R\n");

	if (show_dead)
		cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -d\n");

	if (branch && strcmp(branch, "HEAD"))
		cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -r\n"
			"Argument %s\n",
			branch);

	if (date)
		cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -D\n"
			"Argument %s\n",
			show_date(date, 0, DATE_RFC2822));


	ret = cvs_write(cvs,
			WR_FLUSH,
			"Argument --\n"
			"Argument %s\n"
			"rlist\n",
			cvs->module);

	if (ret == -1)
		die("Cannot send rls command");

	rc = parse_cvs_rls(cvs, rls_path.len ? rls_path.buf : NULL, cb, data);
	strbuf_release(&rls_path);
	return rc;
}

static int verify_revision(const char *revision, const char *entry)
{
	char *rev_start;
	char *rev_end;
	if (entry[0] != '/')
		return -1;

	rev_start = strchr(entry + 1, '/');
	if (!rev_start)
		return -1;

	rev_start++;
	rev_end = strchr(rev_start, '/');
	if (!rev_end)
		return -1;

	if (strncmp(revision, rev_start, rev_end - rev_start))
		return -1;

	return 0;
}

static int parse_mode(const char *str)
{
	int mode = 0;
	int um = 0;
	int mm = 0;
	const char *p = str;
	while (*p) {
		switch (*p) {
		case ',':
			mode |= mm & um;
			mm = 0;
			um = 0;
			break;
		case 'u':
			um |= 0700;
			break;
		case 'g':
			um |= 0070;
			break;
		case 'o':
			um |= 0007;
			break;
		case 'r':
			mm |= 0444;
			break;
		case 'w':
			mm |= 0222;
			break;
		case 'x':
			mm |= 0111;
			break;
		case '=':
			break;
		default:
			return -1;
		}
		p++;
	}
	mode |= mm & mm;
	return mode;
}

/*static char *modestr(int mode)
{
	int mask = 0700;
	int mode_ident;
	struct strbuf mode_sb = STRBUF_INIT;
	while (mask) {
		switch (mask) {
		case 0700:
			strbuf_addstr(&mode_sb, "u=");
			break;
		case 0070:
			strbuf_addstr(&mode_sb, ",g=");
			break;
		case 0007:
			strbuf_addstr(&mode_sb, ",o=");
			break;
		}
		mode_ident = mode & mask;
		if (mode_ident & 0111)
			strbuf_addch(&mode_sb, 'x');
		if (mode_ident & 0222)
			strbuf_addch(&mode_sb, 'w');
		if (mode_ident & 0444)
			strbuf_addch(&mode_sb, 'r');
		mask >>= 3;
	}
	return strbuf_detach(&mode_sb, NULL);
}*/

static void cvsfile_reset(struct cvsfile *file)
{
	strbuf_reset(&file->path);
	strbuf_reset(&file->revision);
	file->isexec = 0;
	file->isdead = 0;
	file->isbin = 0;
	file->ismem = 0;
	file->iscached = 0;
	file->mode = 0;
	file->timestamp = 0;
	strbuf_reset(&file->file);
	file->util = NULL;
}

int cvs_checkout_rev(struct cvs_transport *cvs, const char *file, const char *revision, struct cvsfile *content)
{
	int rc = -1;
	ssize_t ret;

	cvsfile_reset(content);
	strbuf_copystr(&content->path, file);
	strbuf_copystr(&content->revision, revision);

#ifdef DB_CACHE
	int isexec = 0;
	if (!db_cache_get(NULL, file, revision, &isexec, &content->file)) {
		content->isexec = isexec;
		content->ismem = 1;
		content->iscached = 1;
		//tracef("db_cache get file: %s rev: %s size: %zu isexec: %u hash: %u",
		//	file, revision, content->file.len, content->isexec, hash_buf(content->file.buf, content->file.len));
		return 0;
	}
#endif

	ret = cvs_write(cvs,
			WR_FLUSH,
			"Argument -N\n"
			"Argument -P\n"
			"Argument -kk\n"
			"Argument -r\n"
			"Argument %s\n"
			"Argument --\n"
			"Argument %s/%s\n"
			"Directory .\n"
			"%s\n"
			"co\n",
			revision,
			cvs->module, file,
			cvs->repo_path);

	if (ret == -1)
		die("checkout request failed");

	struct strbuf file_full_path = STRBUF_INIT;
	struct strbuf file_mod_path = STRBUF_INIT;
	int mode;
	size_t size;

	strbuf_addstr(&file_full_path, cvs->full_module_path);
	strbuf_complete_line_ch(&file_full_path, '/');
	strbuf_addstr(&file_full_path, file);

	strbuf_addstr(&file_mod_path, cvs->module);
	strbuf_complete_line_ch(&file_mod_path, '/');
	strbuf_addstr(&file_mod_path, file);

	while (1) {
		ret = cvs_readline(cvs, &cvs->rd_line_buf);
		if (ret <= 0)
			return -1;

		if (strbuf_startswith(&cvs->rd_line_buf, "E "))
			tracef("CVS E: %s", cvs->rd_line_buf.buf + 2);

		if (strbuf_startswith(&cvs->rd_line_buf, "Created") ||
		    strbuf_startswith(&cvs->rd_line_buf, "Updated")) {
			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				return -1;
			if (strbuf_cmp(&cvs->rd_line_buf, &file_full_path) &&
			    strbuf_cmp(&cvs->rd_line_buf, &file_mod_path))
				die("Checked out file name doesn't match %s %s", cvs->rd_line_buf.buf, file_full_path.buf);

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				return -1;
			if (verify_revision(revision, cvs->rd_line_buf.buf))
				die("Checked out file revision doesn't match the one requested %s %s", revision, cvs->rd_line_buf.buf);

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				return -1;
			mode = parse_mode(cvs->rd_line_buf.buf);
			if (mode == -1)
				die("Cannot parse checked out file mode %s", cvs->rd_line_buf.buf);
			content->mode = mode;
			content->isexec = !!(mode & 0111);

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				return -1;
			size = atoi(cvs->rd_line_buf.buf);
			if (!size && strcmp(cvs->rd_line_buf.buf, "0"))
				die("Cannot parse file size %s", cvs->rd_line_buf.buf);

			//tracef("checkout %s rev %s mode %o size %zu", file, revision, mode, size);

			if (size) {
				// FIXME:
				if (size <= fileMemoryLimit) {
					content->ismem = 1;

					strbuf_grow(&content->file, size);
					ret = cvs_read_full(cvs, content->file.buf, size);
					if (ret == -1)
						die("Cannot checkout buf");
					if (ret < size)
						die("Cannot checkout buf: truncated: %zu read out of %zu", ret, size);

					strbuf_setlen(&content->file, size);

#ifdef DB_CACHE
					db_cache_add(NULL, file, revision, content->isexec, &content->file);
					//content->iscached = 1;
					//tracef("db_cache add file: %s rev: %s size: %zu isexec: %u hash: %u",
					//	file, revision, content->file.len, content->isexec, hash_buf(content->file.buf, content->file.len));
#endif
				}
				else {
					// FIXME:
					die("Cannot checkout big file %s rev %s size %zu", file, revision, size);
				}
			}

			rc = 0;
		}

		if (strbuf_startswith(&cvs->rd_line_buf, "Removed") ||
		    strbuf_startswith(&cvs->rd_line_buf, "Remove-entry")) {
			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				return -1;
			if (strbuf_cmp(&cvs->rd_line_buf, &file_full_path) &&
			    strbuf_cmp(&cvs->rd_line_buf, &file_mod_path))
				die("Checked out file name doesn't match %s %s", cvs->rd_line_buf.buf, file_full_path.buf);

			content->isdead = 1;
			rc = 0;
		}

		if (!strcmp(cvs->rd_line_buf.buf, "ok"))
			break;

		if (strbuf_startswith(&cvs->rd_line_buf, "error")) {
			tracef("CVS Error: %s", cvs->rd_line_buf.buf);
			break;
		}
	}

	strbuf_release(&file_full_path);
	strbuf_release(&file_mod_path);
	return rc;
}

static int parse_entry(const char *entry, struct strbuf *revision)
{
	char *rev_start;
	char *rev_end;
	if (entry[0] != '/')
		return -1;

	rev_start = strchr(entry + 1, '/');
	if (!rev_start)
		return -1;

	rev_start++;
	rev_end = strchr(rev_start, '/');
	if (!rev_end)
		return -1;

	strbuf_copybuf(revision, rev_start, rev_end - rev_start);
	return 0;
}

void cvsfile_init(struct cvsfile *file)
{
	memset(file, 0, sizeof(*file));
	strbuf_init(&file->path, 0);
	strbuf_init(&file->revision, 0);
	strbuf_init(&file->file, 0);
}

void cvsfile_release(struct cvsfile *file)
{
	strbuf_release(&file->path);
	strbuf_release(&file->revision);
	strbuf_release(&file->file);
}

int cvs_checkout_branch(struct cvs_transport *cvs, const char *branch, time_t date, handle_file_fn_t cb, void *data)
{
	int rc = -1;
	ssize_t ret;
#ifdef DB_CACHE
	int exists = 0;
	DB *db = NULL;
#endif
	if (date) {
#ifdef DB_CACHE
		db = db_cache_init_branch(branch, date, &exists);
		if (db && exists) {
			rc = db_cache_for_each(db, cb, data);
			db_cache_release_branch(db);
			return rc;
		}
#endif

		cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -D\n"
			"Argument %s\n",
			show_date(date, 0, DATE_RFC2822));
	}

	cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -N\n"
			"Argument -P\n"
			"Argument -kk\n");

	if (branch && strcmp(branch, "HEAD"))
		cvs_write(cvs,
			WR_NOFLUSH,
			"Argument -r\n"
			"Argument %s\n",
			branch);


	ret = cvs_write(cvs,
			WR_FLUSH,
			"Argument --\n"
			"Argument %s\n"
			"Directory .\n"
			"%s\n"
			"co\n",
			cvs->module,
			cvs->repo_path);

	if (ret == -1)
		return ret;

	struct strbuf mod_path = STRBUF_INIT;
	struct strbuf mod_time = STRBUF_INIT;
	time_t mod_time_unix = 0;
	struct cvsfile file = CVSFILE_INIT;
	int mode;
	size_t size;


	strbuf_addstr(&mod_path, cvs->module);
	strbuf_complete_line_ch(&mod_path, '/');

	while (1) {
		ret = cvs_readline(cvs, &cvs->rd_line_buf);
		if (ret < 0)
			break;
		if (!ret)
			continue;

		if (strbuf_startswith(&cvs->rd_line_buf, "E "))
			tracef("CVS E: %s", cvs->rd_line_buf.buf + 2);

		if (strbuf_gettext_after(&cvs->rd_line_buf, "Mod-time ", &mod_time)) {
			mod_time_unix = rfc2822_date_to_unixtime(mod_time.buf);
		}

		if (strbuf_startswith(&cvs->rd_line_buf, "Created") ||
		    strbuf_startswith(&cvs->rd_line_buf, "Updated")) {
			cvsfile_reset(&file);
			if (mod_time_unix) {
				file.timestamp = mod_time_unix;
				mod_time_unix = 0;
			}

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				break;
			if (!strbuf_gettext_after(&cvs->rd_line_buf, cvs->full_module_path, &file.path) &&
			    !strbuf_gettext_after(&cvs->rd_line_buf, mod_path.buf, &file.path))
				die("Checked out file name doesn't start with module path %s %s", cvs->rd_line_buf.buf, cvs->full_module_path);

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				break;
			if (parse_entry(cvs->rd_line_buf.buf, &file.revision))
				die("Cannot parse checked out file entry line %s", cvs->rd_line_buf.buf);

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				break;
			mode = parse_mode(cvs->rd_line_buf.buf);
			if (mode == -1)
				die("Cannot parse checked out file mode %s", cvs->rd_line_buf.buf);
			file.mode = mode;
			file.isexec = !!(mode & 0111);

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				break;
			size = atoi(cvs->rd_line_buf.buf);
			if (!size && strcmp(cvs->rd_line_buf.buf, "0"))
				die("Cannot parse file size %s", cvs->rd_line_buf.buf);

			tracef("checkout %s rev %s mode %o size %zu", file.path.buf, file.revision.buf, mode, size);

			if (size) {
				// FIXME:
				if (size <= fileMemoryLimit) {
					file.ismem = 1;
					file.isdead = 0;

					strbuf_grow(&file.file, size);
					ret = cvs_read_full(cvs, file.file.buf, size);
					if (ret == -1)
						die("Cannot checkout buf");
					if (ret < size)
						die("Cannot checkout buf: truncated: %zu read out of %zu", ret, size);

					strbuf_setlen(&file.file, ret);
#ifdef DB_CACHE
					db_cache_add(db, file.path.buf, file.revision.buf, file.isexec, &file.file);
					file.iscached = 1;
					//tracef("db_cache branch add file: %s rev: %s size: %zu isexec: %u hash: %u",
					//	file.path.buf, file.revision.buf, file.file.len, file.isexec, hash_buf(file.file.buf, file.file.len));
#endif
				}
				else {
					// FIXME:
					die("Cannot checkout big file %s rev %s size %zu", file.file.buf, file.revision.buf, size);
				}
			}
			else {
				file.ismem = 1;
			}

			cb(&file, data);
		}

		if (strbuf_startswith(&cvs->rd_line_buf, "Removed") ||
		    strbuf_startswith(&cvs->rd_line_buf, "Remove-entry")) {
			cvsfile_reset(&file);

			if (cvs_readline(cvs, &cvs->rd_line_buf) <= 0)
				break;
			if (!strbuf_gettext_after(&cvs->rd_line_buf, cvs->full_module_path, &file.path) &&
			    !strbuf_gettext_after(&cvs->rd_line_buf, mod_path.buf, &file.path))
				die("Checked out file name doesn't start with module path %s %s", cvs->rd_line_buf.buf, cvs->full_module_path);

			file.isdead = 1;
		}

		if (!strcmp(cvs->rd_line_buf.buf, "ok")) {
			rc = 0;
			break;
		}

		if (strbuf_startswith(&cvs->rd_line_buf, "error")) {
			tracef("CVS Error: %s", cvs->rd_line_buf.buf);
			break;
		}
	}

	cvsfile_release(&file);
	strbuf_release(&mod_path);
	strbuf_release(&mod_time);
#ifdef DB_CACHE
	db_cache_release_branch(db);
#endif
	return rc;
}

static const char *status_replies[] = {
	"Up-to-date",
	"Locally Added",
	"Classify Error",
	"Needs Checkout",
	"Needs Patch",
	"Unresolved Conflict",
	"Locally Removed",
	"File had conflicts on merge",
	"Locally Modified",
	"Needs Merge",
	"Entry Invalid"
};

enum cvs_status
{
	STAT_UP_TO_DATE,
	STAT_LOCALLY_ADDED,
	STAT_CLASSIFY_ERROR,
	STAT_NEEDS_CHECKOUT,
	STAT_NEEDS_PATCH,
	STAT_UNRESOLVED_CONFLICT,
	STAT_LOCALLY_REMOVED,
	STAT_FILE_HAD_CONFLICTS_ON_MERGE,
	STAT_LOCALLY_MODIFIED,
	STAT_NEEDS_MERGE,
	STAT_ENTRY_INVALID,
	STAT_UNKNOWN
};

int parse_status_state(const char *status)
{
	int i;
	for (i = 0; i < STAT_UNKNOWN; i++)
		if (!strcmp(status, status_replies[i]))
			return i;

	error("unknown cvs status reply: \"%s\"", status);
	return STAT_UNKNOWN;
}

static struct cvsfile *cvsfile_find(struct cvsfile *files, int count, const char *path)
{
	int i;
	/*
	 * TODO: list is sorted, do a binary search
	 */

	for (i = 0; i < count; i++)
		if (!strcmp(files[i].path.buf, path))
			return &files[i];

	return NULL;
}

#define CVS_FILE_STATUS_START "==================================================================="
enum
{
	NEED_START_STATUS		= 0,
	NEED_FILE_STATUS		= 1,
	NEED_WORKING_REVISION		= 2,
	NEED_REPOSITORY_REVISION	= 3
};

static int parse_update_cvs_status(struct cvs_transport *cvs, struct cvsfile *files, int count)
{
	struct strbuf line = STRBUF_INIT;
	struct strbuf buf = STRBUF_INIT;
	struct strbuf current_dir = STRBUF_INIT;
	struct strbuf file_basename = STRBUF_INIT;
	struct strbuf path = STRBUF_INIT;
	struct strbuf status = STRBUF_INIT;
	struct strbuf local_rev = STRBUF_INIT;
	struct strbuf remote_rev = STRBUF_INIT;
	struct cvsfile *file;
	ssize_t ret;
	char *p;
	int status_state;
	int rc = 0;

	int state = NEED_START_STATUS;

	while (1) {
		ret = cvs_readline(cvs, &cvs->rd_line_buf);
		if (ret <= 0) {
			rc = -1;
			break;
		}

		if (strbuf_startswith(&cvs->rd_line_buf, "E ")) {
			if (!strbuf_gettext_after(&cvs->rd_line_buf, "E cvs status: Examining ", &current_dir))
				tracef("CVS E: %s", cvs->rd_line_buf.buf + 2);
		}

		if (strbuf_gettext_after(&cvs->rd_line_buf, "M ", &line)) {
/*
M ===================================================================\0a
M File: neeeeeeeewws     \09Status: Up-to-date\0a
M \0a
M    Working revision:\091.1.2.2\0a
M    Repository revision:\091.1.2.2\09/home/dummy/devel/SVC/cvs/src/dir/neeeeeeeewws,v\0a
M    Sticky Tag:\09\09mybranch (branch: 1.1.2)\0a
M    Sticky Date:\09\09(none)\0a
M    Sticky Options:\09(none)\0a
M \0a
E cvs status: Examining dir/some\0a
E cvs status: Examining dir/some/new\0a
M ===================================================================\0a
M File: file_in_dirs     \09Status: Locally Added\0a
M \0a
M    Working revision:\09New file!\0a
M    Repository revision:\09No revision control file\0a
M    Sticky Tag:\09\09mybranch - MISSING from RCS file!\0a
M    Sticky Date:\09\09(none)\0a
M    Sticky Options:\09(none)\0a

adding file that was removed (status done with version '0', reply should contain actual deleve revision)
M ===================================================================
M File: file             \tStatus: Locally Added
M 
M    Working revision:\tNew file!
M    Repository revision:\t1.2\t/home/dummy/tmp/moo/cvs_repo/mod/src/somedir/Attic/file,v
M    Sticky Tag:\t\t(none)
M    Sticky Date:\t\t(none)
M    Sticky Options:\t(none)
M
cvs status: `src/remove_me' is no longer in the repository
===================================================================
File: remove_me        	Status: Entry Invalid

   Working revision:	1.1	2014-03-24 16:02:25 +0100
   Repository revision:	1.2	/home/dummy/tmp/moo/cvs_repo/mod/src/Attic/remove_me,v
   Commit Identifier:	(none)
   Sticky Tag:		(none)
   Sticky Date:		(none)
   Sticky Options:	(none)
*/
			switch (state) {
			case NEED_START_STATUS:
				if (strbuf_startswith(&line, CVS_FILE_STATUS_START)) {
					strbuf_reset(&file_basename);
					strbuf_reset(&path);
					strbuf_reset(&status);
					strbuf_reset(&local_rev);
					strbuf_reset(&remote_rev);
					state = NEED_FILE_STATUS;
				}
				break;
			case NEED_FILE_STATUS:
				if (strbuf_gettext_after(&line, "File: ", &buf)) {
					p = strchr(buf.buf, '\t');
					if (!p)
						die("Cannot parse CVS status line file %s", line.buf);
					strbuf_add(&file_basename, buf.buf, p - buf.buf);
					strbuf_trim(&file_basename);

					strbuf_remove(&buf, 0, p+1 - buf.buf);
					if (!strbuf_gettext_after(&buf, "Status: ", &status))
						die("Cannot parse CVS status line status %s", line.buf);
					state = NEED_WORKING_REVISION;
				}
				break;
			case NEED_WORKING_REVISION:
				strbuf_trim(&line);
				if (strbuf_gettext_after(&line, "Working revision:", &local_rev)) {
					strbuf_trim(&local_rev);
					p = strchr(local_rev.buf, '\t');
					if (p)
						strbuf_setlen(&local_rev, p - local_rev.buf);
					state = NEED_REPOSITORY_REVISION;
				}
				break;
			case NEED_REPOSITORY_REVISION:
				strbuf_trim(&line);
				if (strbuf_gettext_after(&line, "Repository revision:", &remote_rev)) {
					strbuf_trim(&remote_rev);
					p = strchr(remote_rev.buf, '\t');
					if (p) {
						strbuf_addstr(&path, p);
						strbuf_trim(&path);
						if (!suffixcmp(path.buf, ",v"))
							strbuf_setlen(&path, path.len - 2);
						strbuf_setlen(&remote_rev, p - remote_rev.buf);
						p = strstr(path.buf, "/Attic/");
						if (p)
							strbuf_remove(&path, p - path.buf, strlen("/Attic"));
						if (prefixcmp(path.buf, cvs->full_module_path))
							die("File status path does not start with repository path");
						strbuf_remove(&path, 0, strlen(cvs->full_module_path));
					}
					else if (current_dir.len) {
						if (!strcmp(current_dir.buf, "."))
							strbuf_copy(&path, &file_basename);
						else
							strbuf_addf(&path, "%s/%s", current_dir.buf, file_basename.buf);
					}

					tracef("file: %s status: %s rev local: %s rev remote: %s",
						path.buf, status.buf, local_rev.buf, remote_rev.buf);

					file = cvsfile_find(files, count, path.buf);
					if (!file) {
						error("File status, found status for not requested file: %s", path.buf);
						state = NEED_START_STATUS;
						continue;
					}

					status_state = parse_status_state(status.buf);
					switch (status_state) {
					case STAT_UP_TO_DATE:
						break;
					case STAT_LOCALLY_ADDED:
						if (file->isdead) {
							if (strcmp(file->revision.buf, remote_rev.buf)) {
								tracef("File status: %s was removed in cvs, adding again now. "
										"Repository revision: %s Expected %s. Metadata corrupt?\n",
										file->path.buf, remote_rev.buf, file->revision.buf);
								rc = 1;
							}
						}
						else if (!file->isnew) {
							rc = 1;
						}
						break;
					/*
					 * STAT_ENTRY_INVALID is reported when file is removed.
					 */
					case STAT_ENTRY_INVALID:
						file->isdead = 1;
						/* fall through */
					default:
						rc = 1;
					}
					file->handled = 1;
					state = NEED_START_STATUS;
					strbuf_copy(&file->revision, &remote_rev);
				}
				break;
			}
		}

		if (!strcmp(cvs->rd_line_buf.buf, "ok"))
			break;

		if (strbuf_startswith(&cvs->rd_line_buf, "error")) {
			tracef("CVS Error: %s", cvs->rd_line_buf.buf);
			rc = -1;
			break;
		}
	}

	struct cvsfile *file_it = files;
	while (file_it < files + count) {
		if (!file_it->handled)
			die("Did not get status for file: %s", file_it->path.buf);
		file_it++;
	}

	strbuf_release(&line);
	strbuf_release(&buf);
	strbuf_release(&current_dir);
	strbuf_release(&file_basename);
	strbuf_release(&path);
	strbuf_release(&status);
	strbuf_release(&local_rev);
	strbuf_release(&remote_rev);
	return rc;
}

int cvs_status(struct cvs_transport *cvs, const char *cvs_branch, struct cvsfile *files, int count)
{
/*
"Argument --\n
Directory .\n
/home/dummy/devel/SVC/cvs2/sources/smod\n
Sticky Tunstable\n
Entry /EXPERIMENTAL/1.1.4.2///Tunstable\n
Unchanged EXPERIMENTAL\n
Entry /Makefile/1.3.2.2///Tunstable\n
Unchanged Makefile\n
Entry /TODO/1.2.2.2///Tunstable\n
Unchanged TODO\n
Directory include\n
/home/dummy/devel/SVC/cvs2/sources/smod/include\n
Sticky Tunstable\n
Entry /lib.h/1.1.2.1///Tunstable\n
Unchanged lib.h\n
Entry /util.h/1.1///Tunstable\n
Unchanged util.h\n
Directory lib\n
/home/dummy/devel/SVC/cvs2/sources/smod/lib\n
Sticky Tunstable\n
Entry /lib.c/1.1.2.2///Tunstable\n
Unchanged lib.c\n
Directory src\n
/home/dummy/devel/SVC/cvs2/sources/smod/src\n
Sticky Tunstable\n
Entry /daemon.c/1.2.2.1///Tunstable\n
Unchanged daemon.c\n
Entry /lib_adapter.c/1.1.2.1///Tunstable\n
Unchanged lib_adapter.c\n
Entry /util.c/1.2///Tunstable\n
Unchanged util.c\n
Directory .\n
/home/dummy/devel/SVC/cvs2/sources/smod\n
Sticky Tunstable\n
Argument .\n
status\n
"
*/
	struct strbuf file_basename_sb = STRBUF_INIT;
	struct strbuf dir_repo_relative_sb = STRBUF_INIT;
	struct strbuf dir_sb = STRBUF_INIT;
	int sticky;
	const char *dir;
	ssize_t ret;

	sticky = !!strcmp(cvs_branch, "HEAD");

	cvs_write(cvs, WR_NOFLUSH, "Argument --\n");

	struct cvsfile *file_it = files;
	while (file_it < files + count) {
		strbuf_copystr(&file_basename_sb, basename(file_it->path.buf));
		strbuf_copy(&dir_sb, &file_it->path);
		dir = dirname(dir_sb.buf); // "." (dot) is what we want here if no directory in path
		if (strcmp(dir, dir_repo_relative_sb.buf)) {
			strbuf_copystr(&dir_repo_relative_sb, dir);
			cvs_write(cvs, WR_NOFLUSH,
					"Directory %s\n",
					dir_repo_relative_sb.buf);

			if (!strcmp(dir_repo_relative_sb.buf, ".")) {
				cvs_write(cvs, WR_NOFLUSH,
					"%s/%s\n",
					cvs->repo_path, cvs->module);
			}
			else {
				cvs_write(cvs, WR_NOFLUSH,
					"%s/%s/%s\n",
					cvs->repo_path, cvs->module, dir_repo_relative_sb.buf);
			}

			if (sticky) {
				cvs_write(cvs, WR_NOFLUSH,
					"Sticky T%s\n",
					cvs_branch);
			}
		}

		cvs_write(cvs, WR_NOFLUSH,
					"Entry /%s/%s//-kk/%s%s\n"
					"Unchanged %s\n",
					file_basename_sb.buf,
					!file_it->isdead && file_it->revision.len ? file_it->revision.buf : "0",
					sticky ? "T" : "", sticky ? cvs_branch : "",
					file_basename_sb.buf);
		file_it++;
	}

	cvs_write(cvs, WR_NOFLUSH,	"Directory .\n"
					"%s/%s\n",
					cvs->repo_path, cvs->module);

	if (sticky) {
		cvs_write(cvs, WR_NOFLUSH,
					"Sticky T%s\n",
					cvs_branch);
	}

	ret = cvs_write(cvs, WR_FLUSH, "status\n");

	if (ret == -1)
		die("cvs status failed");

	strbuf_release(&file_basename_sb);
	strbuf_release(&dir_repo_relative_sb);
	strbuf_release(&dir_sb);
	return parse_update_cvs_status(cvs, files, count);
}

int cvs_create_directories(struct cvs_transport *cvs, const char *cvs_branch, struct string_list *new_directory_list)
{
/*
"
Argument --\n
Directory .\n
/home/dummy/devel/SVC/cvs2/sources/smod\n
Sticky Tunstable\n
Directory include\n
/home/dummy/devel/SVC/cvs2/sources/smod/include\n
Sticky Tunstable\n
Directory .\n
/home/dummy/devel/SVC/cvs2/sources/smod\n
Sticky Tunstable\n
Directory include/export\n
/home/dummy/devel/SVC/cvs2/sources/smod/include/export\n
Sticky Tunstable\n
Directory include/import\n
/home/dummy/devel/SVC/cvs2/sources/smod/include/import\n
Sticky Tunstable\n
Directory impl\n
/home/dummy/devel/SVC/cvs2/sources/smod/impl\n
Sticky Tunstable\n
Directory .\n
/home/dummy/devel/SVC/cvs2/sources/smod\n
Sticky Tunstable\n
Argument include/export\n
Argument include/import\n
Argument impl\n
add\n
"*/

	struct strbuf reply = STRBUF_INIT;
	struct strbuf dir_sb = STRBUF_INIT;
	int sticky;
	char *dir;
	ssize_t ret;
	struct string_list_item *item;

	sticky = !!strcmp(cvs_branch, "HEAD");
	cvs_write(cvs, WR_NOFLUSH, "Argument --\n");

	/*
	 * For some reason CVS require directory traversal
	 */
	struct string_list dir_traversal_list = STRING_LIST_INIT_DUP;
	for_each_string_list_item(item, new_directory_list) {
		strbuf_copystr(&dir_sb, item->string);
		dir = dir_sb.buf;
		do {
			string_list_insert(&dir_traversal_list, dir);
		} while ((dir = dirname(dir)) && strcmp(dir, "."));
	}

	strbuf_copystr(&dir_sb, ".");
	sort_string_list(&dir_traversal_list);
	string_list_remove_duplicates(&dir_traversal_list, 0);
	for_each_string_list_item(item, &dir_traversal_list) {
		if (prefixcmp(item->string, dir_sb.buf)) {
			cvs_write(cvs, WR_NOFLUSH,
					"Directory .\n"
					"%s/%s\n",
					cvs->repo_path, cvs->module);
			if (sticky) {
				cvs_write(cvs, WR_NOFLUSH,
					"Sticky T%s\n",
					cvs_branch);
			}
			strbuf_copystr(&dir_sb, item->string);
		}

		cvs_write(cvs, WR_NOFLUSH,
					"Directory %s\n"
					"%s/%s/%s\n",
					item->string,
					cvs->repo_path, cvs->module, item->string);
		if (sticky) {
			cvs_write(cvs, WR_NOFLUSH,
					"Sticky T%s\n",
					cvs_branch);
		}
	}
	strbuf_release(&dir_sb);
	string_list_clear(&dir_traversal_list, 0);

	cvs_write(cvs, WR_NOFLUSH,	"Directory .\n"
					"%s/%s\n",
					cvs->repo_path, cvs->module);
	if (sticky) {
		cvs_write(cvs, WR_NOFLUSH,
					"Sticky T%s\n",
					cvs_branch);
	}
	for_each_string_list_item(item, new_directory_list) {
		cvs_write(cvs, WR_NOFLUSH, "Argument %s\n", item->string);
	}
	ret = cvs_write(cvs, WR_FLUSH, "add\n");

	if (ret == -1)
		die("cvs status failed");

/*
 * TODO: verify directories added
M Directory /home/dummy/devel/SVC/cvs/src/dir/some added to the repository\0a
M --> Using per-directory sticky tag `mybranch'\0a
M Directory /home/dummy/devel/SVC/cvs/src/dir/some/new added to the repository\0a
M --> Using per-directory sticky tag `mybranch'\0a
*/
	ret = cvs_getreply(cvs, &reply, "ok");
	strbuf_release(&reply);
	if (ret)
		return -1;

	return 0;
}

int inc_revision(struct strbuf *rev_sb)
{
	int num;
	char *p = strrchr(rev_sb->buf, '.');
	if (!p || !(num = atoi(++p)))
		return -1;

	strbuf_setlen(rev_sb, p - rev_sb->buf);
	strbuf_addf(rev_sb, "%d", ++num);
	return 0;
}

enum
{
	NEED_CHECK_IN		= 0,
	NEED_NEW_REVISION	= 1,
	NEED_DONE		= 2
};

static int parse_cvs_checkin_reply(struct cvs_transport *cvs, const char *cvs_branch, struct cvsfile *files, int count)
{
	struct strbuf line = STRBUF_INIT;
	struct strbuf buf = STRBUF_INIT;
	struct strbuf repo_mod_path = STRBUF_INIT;
	struct strbuf path = STRBUF_INIT;
	struct strbuf new_rev = STRBUF_INIT;
	struct strbuf old_rev = STRBUF_INIT;
	struct cvsfile *file;
	ssize_t ret;
	char *p;
	int rc = 0;

	int state = NEED_CHECK_IN;

	strbuf_addf(&repo_mod_path, "%s/%s/", cvs->repo_path, cvs->module);
/*
"M ? impl/new\n
M RCS file: /home/dummy/devel/SVC/cvs2/sources/smod/impl/Attic/decorator.impl,v\n
M done\n
M Checking in impl/decorator.impl;\n
M /home/dummy/devel/SVC/cvs2/sources/smod/impl/Attic/decorator.impl,v  <--  decorator.impl\n
M new revision: 1.1.2.1; previous revision: 1.1\n
M done\n
Mode u=rw,g=rw,o=r\n
Checked-in impl/\n
/home/dummy/devel/SVC/cvs2/sources/smod/impl/decorator.impl\n
/decorator.impl/1.1.2.1///Tunstable\n

M Checking in include/util.h;\n
M /home/dummy/devel/SVC/cvs2/sources/smod/include/util.h,v  <--  util.h\n
M new revision: 1.1.2.1; previous revision: 1.1\n
M done\n
Mode u=rw,g=rw,o=r\n
Checked-in include/\n
/home/dummy/devel/SVC/cvs2/sources/smod/include/util.h\n
/util.h/1.1.2.1///Tunstable\n
ok\n"

CVS   65 <- M /home/dummy/tmp/moo/cvs_repo/mod/src/Makefile,v  <--  Makefile\0a
CVS   24 <- M initial revision: 1.1\0a
CVS   19 <- Mode u=rw,g=rw,o=r\0a
CVS   14 <- Checked-in ./\0a
CVS   17 <- mod/src/Makefile\0a
CVS   20 <- /Makefile/1.1//-kk/\0a

CVS  107 <- M /home/dummy/tmp/moo/cvs_repo/mod/src/lib/Transforms/Scalar/DCE.cpp,v  <--  lib/Transforms/Scalar/DCE.cpp\0a
CVS   44 <- M new revision: 1.6; previous revision: 1.5\0a
CVS   19 <- Mode u=rw,g=rw,o=r\0a
CVS   34 <- Checked-in lib/Transforms/Scalar/\0a
CVS   38 <- mod/src/lib/Transforms/Scalar/DCE.cpp\0a
CVS   19 <- /DCE.cpp/1.6//-kk/\0a
*/
	while (1) {
		ret = cvs_readline(cvs, &cvs->rd_line_buf);
		if (ret <= 0) {
			rc = -1;
			break;
		}

		if (strbuf_startswith(&cvs->rd_line_buf, "E ")) {
			tracef("CVS E: %s", cvs->rd_line_buf.buf + 2);
			fprintf(stderr, "CVS E: %s\n", cvs->rd_line_buf.buf + 2);
		}

		if (!prefixcmp(cvs->rd_line_buf.buf, "Checked-in ") ||
		    !prefixcmp(cvs->rd_line_buf.buf, "Remove-entry ")) {
			if (state != NEED_DONE)
				die("skipped file during parsing checkin reply");
			state = NEED_CHECK_IN;
		}

		if (strbuf_gettext_after(&cvs->rd_line_buf, "M ", &line)) {
			tracef("CVS M: %s", cvs->rd_line_buf.buf + 2);
			fprintf(stderr, "CVS M: %s\n", cvs->rd_line_buf.buf + 2);
			switch (state) {
			case NEED_CHECK_IN:
				if (strbuf_gettext_after(&line, repo_mod_path.buf, &path)) {
					p = strstr(path.buf, ",v  <--  ");
					if (!p)
						die("checkin path doesn't match expected pattern: '%s'", line.buf);

					strbuf_setlen(&path, p - path.buf);
					p = strstr(path.buf, "Attic/");
					if (p)
						strbuf_remove(&path, p - path.buf, strlen("Attic/"));
					state = NEED_NEW_REVISION;
				}
				break;
			case NEED_NEW_REVISION:
				if (strbuf_gettext_after(&line, "new revision: ", &buf)) {
					p = strchr(buf.buf, ';');
					if (!p)
						error("Checkin file cannot parse new revision line: %s", line.buf);
					else {
						strbuf_add(&new_rev, buf.buf, p - buf.buf);
						if (!prefixcmp(p, "; previous revision: ")) {
							p += strlen("; previous revision: ");
							strbuf_addstr(&old_rev, p);
						}
					}

					if (!strcmp(new_rev.buf, "delete")) {
						strbuf_copy(&new_rev, &old_rev);
						/*
						 * cvs server does not tell new revision if file is
						 * deleted, but for HEAD it is straight forward, just
						 * minor version increase. For branches it is tricky
						 * and if file was unchanged since branch fork, the
						 * revision will change dramatically and hard to
						 * guess. So, old revision is left here, and later
						 * filled in with extra cvs status call.
						 */
						if (!strcmp(cvs_branch, "HEAD"))
							inc_revision(&new_rev);
					}
				}
				else if (strbuf_gettext_after(&line, "initial revision: ", &new_rev)) {
					/*
					 * TODO: validate
					 */
				}
				else {
					continue;
				}

				file = cvsfile_find(files, count, path.buf);
				if (!file)
					die("Checkin file info found for not requested file: %s", path.buf);
				else if (strcmp(file->revision.buf, old_rev.buf) && !file->isnew) {
					error("Checkin file %s old revision %s, but %s is reported",
					      path.buf, file->revision.buf, old_rev.buf);
					strbuf_copy(&file->revision, &new_rev);
				}
				else {
					strbuf_copy(&file->revision, &new_rev);
				}
				file->handled = 1;

				strbuf_reset(&path);
				strbuf_reset(&new_rev);
				strbuf_reset(&old_rev);
				state = NEED_DONE;
				break;
			/*
			case NEED_CHECK_IN:
				if (strbuf_gettext_after(&line, "Checking in ", &path) ||
				    strbuf_gettext_after(&line, "Removing ", &path)) {
					p = strchr(path.buf, ';');
					if (p)
						strbuf_setlen(&path, p - path.buf);
					state = NEED_NEW_REVISION;
				}
				break;
			case NEED_NEW_REVISION:
				if (strbuf_gettext_after(&line, "new revision: ", &buf)) {
					p = strchr(buf.buf, ';');
					if (!p)
						error("Checkin file cannot parse new revision line: %s", line.buf);
					else {
						strbuf_add(&new_rev, buf.buf, p - buf.buf);
						if (!prefixcmp(p, "; previous revision: ")) {
							p += strlen("; previous revision: ");
							strbuf_addstr(&old_rev, p);
						}
					}
					state = NEED_DONE;
				}
				break;
			case NEED_DONE:
				if (!strcmp(line.buf, "done")) {
					file = cvsfile_find(files, count, path.buf);
					if (!file)
						error("Checkin file info found for not requested file: %s", path.buf);
					else if (strcmp(file->revision.buf, old_rev.buf) && !file->isnew) {
						error("Checkin file %s old revision %s, but %s is reported",
						      path.buf, file->revision.buf, old_rev.buf);
						strbuf_copy(&file->revision, &new_rev);
					}
					else {
						strbuf_copy(&file->revision, &new_rev);
					}

					strbuf_reset(&path);
					strbuf_reset(&new_rev);
					strbuf_reset(&old_rev);
					state = NEED_CHECK_IN;
				}
				break;*/
			}
		}

		if (!strcmp(cvs->rd_line_buf.buf, "ok"))
			break;

		if (strbuf_startswith(&cvs->rd_line_buf, "error")) {
			tracef("CVS Error: %s", cvs->rd_line_buf.buf);
			rc = -1;
			break;
		}
	}

	struct cvsfile *file_it = files;
	while (file_it < files + count) {
		if (!file_it->handled)
			die("Did not get checking confirmation for file: %s", file_it->path.buf);
		file_it++;
	}

	strbuf_release(&line);
	strbuf_release(&buf);
	strbuf_release(&repo_mod_path);
	strbuf_release(&path);
	strbuf_release(&new_rev);
	strbuf_release(&old_rev);
	return rc;
}

extern int is_prev_rev(const char *rev1, const char *rev2);
int cvs_get_deleted_files_revisions(struct cvs_transport *cvs, const char *cvs_branch, struct cvsfile *allfiles, int count)
{
	struct cvsfile *files;
	struct cvsfile *file_it;
	int deleted_count = 0;
	int rc;
	int i;

	for (file_it = allfiles; file_it < allfiles + count; file_it++) {
		if (file_it->isdead)
			deleted_count++;
	}

	files = xcalloc(deleted_count, sizeof(*files));
	for (file_it = allfiles, i = 0; file_it < allfiles + count; file_it++) {
		if (!file_it->isdead)
			continue;

		cvsfile_init(&files[i]);
		strbuf_addbuf(&files[i].path, &file_it->path);
		strbuf_addbuf(&files[i].revision, &file_it->revision);
		//files[i].isdead = file_it->isdead;

		tracef("status: %s rev: %s isdead: %u",
			files[i].path.buf, files[i].revision.buf, files[i].isdead);
		i++;
	}

	rc = cvs_status(cvs, cvs_branch, files, deleted_count);
	if (rc == -1 || rc == 0) {
		error("cvs commit succeded, but cannot update metadata, due to failed cvs status on deleted files");
		rc = -1;
	}
	else {
		rc = 0;
		for (file_it = allfiles, i = 0; file_it < allfiles + count; file_it++) {
			if (!file_it->isdead)
				continue;

			tracef("status for deleted file: %s rev: %s newrev: %s",
				files[i].path.buf, file_it->revision.buf, files[i].revision.buf);

			if (!is_prev_rev(file_it->revision.buf, files[i].revision.buf)) {
				error("status for deleted file: %s rev: %s newrev: %s not sequential",
					files[i].path.buf, file_it->revision.buf, files[i].revision.buf);
				rc = -1;
			}
			strbuf_copy(&file_it->revision, &files[i].revision);
			i++;
		}
	}

	for (i = 0; i < deleted_count; i++)
		cvsfile_release(&files[i]);
	free(files);
	return rc;
}

int cvs_checkin(struct cvs_transport *cvs, const char *cvs_branch, const char *message,
			struct cvsfile *files, int count,
			prepare_file_content_fn_t prepare_file_cb,
			release_file_content_fn_t release_file_cb,
			void *data)
{
/*
"Argument -m\n
Argument do it\n
Argumentx \n
Directory impl\n
/home/dummy/devel/SVC/cvs2/sources/smod/impl\n
Questionable new\n
Argument --\n
Directory impl\n
/home/dummy/devel/SVC/cvs2/sources/smod/impl\n
Sticky Tunstable\n
Entry /decorator.impl/0///Tunstable\n
Modified decorator.impl\n
u=rw,g=rw,o=r\n
22\n
# TODO\n
# add to build\n
Directory include\n
/home/dummy/devel/SVC/cvs2/sources/smod/include\n
Sticky Tunstable\n
Entry /util.h/1.1///Tunstable\n
Modified util.h\n
u=rw,g=rw,o=r\n
51\n
**\n
 * TODO: comments\n
 **\n
\n
extern void utils(void);\n
Directory .\n
/home/dummy/devel/SVC/cvs2/sources/smod\n
Sticky Tunstable\n
Argument impl/decorator.impl\n
Argument include/util.h\n
ci\n
"
*/
/*
"Argument -m\n
Argument remove it\n
Argumentx \n
Argument --\n
Directory src\n
/home/dummy/devel/SVC/cvs2/sources/smod/src\n
Sticky Tunstable\n
Entry /lib_adapter.c/-1.1.2.1///Tunstable\n
Directory .\n
/home/dummy/devel/SVC/cvs2/sources/smod\n
Sticky Tunstable\n
Argument src/lib_adapter.c\n
ci\n
"
*/

	struct strbuf file_basename_sb = STRBUF_INIT;
	struct strbuf dir_repo_relative_sb = STRBUF_INIT;
	struct strbuf dir_sb = STRBUF_INIT;
	struct strbuf **lines, **it;
	int sticky;
	int has_file_removes = 0;
	const char *dir;
	ssize_t ret;

	sticky = !!strcmp(cvs_branch, "HEAD");

	cvs_write(cvs, WR_NOFLUSH, "Argument -m\n");
	lines = strbuf_split_buf(message, strlen(message), '\n', 0);
	for (it = lines; *it; it++) {
		strbuf_rtrim(*it);
		if (it == lines)
			cvs_write(cvs, WR_NOFLUSH, "Argument %s\n", (*it)->buf);
		else
			cvs_write(cvs, WR_NOFLUSH, "Argumentx %s\n", (*it)->buf);
	}
	strbuf_list_free(lines);
	cvs_write(cvs, WR_NOFLUSH, "Argument --\n");

	struct cvsfile *file_it = files;
	while (file_it < files + count) {
		if (prepare_file_cb(file_it, data))
			die("prepare checkin file failed: %s", file_it->path.buf);

		strbuf_copystr(&file_basename_sb, basename(file_it->path.buf));
		strbuf_copy(&dir_sb, &file_it->path);
		dir = dirname(dir_sb.buf); // "." (dot) is what we want here if no directory in path
		if (strcmp(dir, dir_repo_relative_sb.buf)) {
			strbuf_copystr(&dir_repo_relative_sb, dir);
			cvs_write(cvs, WR_NOFLUSH,
					"Directory %s\n",
					dir_repo_relative_sb.buf);

			if (!strcmp(dir_repo_relative_sb.buf, ".")) {
				cvs_write(cvs, WR_NOFLUSH,
					"%s/%s\n",
					cvs->repo_path, cvs->module);
			}
			else {
				cvs_write(cvs, WR_NOFLUSH,
					"%s/%s/%s\n",
					cvs->repo_path, cvs->module, dir_repo_relative_sb.buf);
			}

			if (sticky) {
				cvs_write(cvs, WR_NOFLUSH,
					"Sticky T%s\n",
					cvs_branch);
			}
		}

		if (!file_it->isdead) {
			cvs_write(cvs, WR_NOFLUSH,
					"Entry /%s/%s//-kk/%s%s\n"
					"Modified %s\n"
					"%s\n",
					file_basename_sb.buf,
					file_it->revision.len ? file_it->revision.buf : "0",
					sticky ? "T" : "", sticky ? cvs_branch : "",
					file_basename_sb.buf,
					file_it->isexec ? "u=rwx,g=rwx,o=rx" : "u=rw,g=rw,o=r");
			cvs_write(cvs, WR_FLUSH, "%zu\n", file_it->file.len);
			if (file_it->file.len)
				cvs_write_full(cvs, file_it->file.buf, file_it->file.len);
		}
		else {
			cvs_write(cvs, WR_NOFLUSH,
					"Entry /%s/-%s//-kk/%s%s\n",
					file_basename_sb.buf,
					file_it->revision.buf,
					sticky ? "T" : "",
					sticky ? cvs_branch : "");
			has_file_removes = 1;
		}
		release_file_cb(file_it, data);
		file_it++;
	}

	cvs_write(cvs, WR_NOFLUSH,	"Directory .\n"
					"%s/%s\n",
					cvs->repo_path, cvs->module);

	if (sticky) {
		cvs_write(cvs, WR_NOFLUSH,
					"Sticky T%s\n",
					cvs_branch);
	}

	file_it = files;
	while (file_it < files + count) {
		cvs_write(cvs, WR_NOFLUSH,
					"Argument %s\n",
					file_it->path.buf);
		file_it++;
	}

	ret = cvs_write(cvs, WR_FLUSH, "ci\n");
	if (ret == -1)
		die("Cannot send checkin command");

	strbuf_release(&file_basename_sb);
	strbuf_release(&dir_repo_relative_sb);
	strbuf_release(&dir_sb);

	ret = parse_cvs_checkin_reply(cvs, cvs_branch, files, count);
	if (ret) {
		error("parse_cvs_checkin_reply failed");
		return ret;
	}

	if (strcmp(cvs_branch, "HEAD") && has_file_removes)
		ret = cvs_get_deleted_files_revisions(cvs, cvs_branch, files, count);

	return ret;
}

char *cvs_get_rev_branch(struct cvs_transport *cvs, const char *file, const char *revision)
{
	ssize_t ret;
	ret = cvs_write(cvs,
			WR_FLUSH,
			"Argument -h\n"
			"Argument --\n"
			"Argument %s/%s\n"
			"rlog\n",
			cvs->module, file);
	if (ret == -1)
		die("Cannot send rlog command");

	struct strbuf reply = STRBUF_INIT;
	struct strbuf branch = STRBUF_INIT;

	struct strbuf branch_name = STRBUF_INIT;
	struct strbuf branch_rev = STRBUF_INIT;

	size_t len;
	strbuf_grow(&reply, CVS_MAX_LINE);
	int state = NEED_RCS_FILE;
	int found = 0;

	strbuf_addstr(&branch, revision);
	strip_last_rev_num(&branch);

	while (1) {
		ret = cvs_getreply_firstmatch(cvs, &reply, "M ");
		if (ret == -1)
			return NULL;
		else if (ret == 1) /* ok from server */
			break;

		len = strlen(reply.buf);
		strbuf_setlen(&reply, len);
		if (len && reply.buf[len - 1] == '\n')
			strbuf_setlen(&reply, len - 1);

		switch(state) {
		case NEED_RCS_FILE:
			if (!prefixcmp(reply.buf, "RCS file: "))
				state = NEED_SYMS;
			break;
		case NEED_SYMS:
			if (!prefixcmp(reply.buf, "symbolic names:"))
				state = NEED_EOS;
			break;
		case NEED_EOS:
			if (!isspace(reply.buf[0])) {
				state = SKIP_LINES;
			}
			else {
				strbuf_ltrim(&reply);

				if (parse_sym(&reply, &branch_name, &branch_rev) == sym_branch &&
				    !strbuf_cmp(&branch_rev, &branch)) {
					found = 1;
					state = SKIP_LINES;
				}
			}
			break;
		default:
			break;
		}
	}

	if (state != SKIP_LINES)
		die("Cannot parse revision rlog, parser state %d", state);

	strbuf_release(&branch_rev);
	strbuf_release(&reply);
	strbuf_release(&branch);

	if (found)
		return strbuf_detach(&branch_name, NULL);

	strbuf_release(&branch_name);
	return NULL;
}

int cvs_tag(struct cvs_transport *cvs, const char *cvs_branch, int istag, struct cvsfile *files, int count)
{
	struct strbuf reply = STRBUF_INIT;
	struct strbuf file_basename_sb = STRBUF_INIT;
	struct strbuf dir_repo_relative_sb = STRBUF_INIT;
	struct strbuf dir_sb = STRBUF_INIT;
	const char *dir;
	ssize_t ret;
	int rc = -1;

	if (!istag)
		cvs_write(cvs, WR_NOFLUSH, "Argument -b\n");

	cvs_write(cvs, WR_NOFLUSH, "Argument --\n"
				   "Argument %s\n",
				   cvs_branch);

	struct cvsfile *file_it = files;
	while (file_it < files + count) {
		strbuf_copystr(&file_basename_sb, basename(file_it->path.buf));
		strbuf_copy(&dir_sb, &file_it->path);
		dir = dirname(dir_sb.buf); // "." (dot) is what we want here if no directory in path
		if (strcmp(dir, dir_repo_relative_sb.buf)) {
			strbuf_copystr(&dir_repo_relative_sb, dir);
			cvs_write(cvs, WR_NOFLUSH,
					"Directory %s\n",
					dir_repo_relative_sb.buf);

			if (!strcmp(dir_repo_relative_sb.buf, ".")) {
				cvs_write(cvs, WR_NOFLUSH,
					"%s/%s\n",
					cvs->repo_path, cvs->module);
			}
			else {
				cvs_write(cvs, WR_NOFLUSH,
					"%s/%s/%s\n",
					cvs->repo_path, cvs->module, dir_repo_relative_sb.buf);
			}
		}

		cvs_write(cvs, WR_NOFLUSH,
					"Entry /%s/%s///\n"
					"Unchanged %s\n",
					file_basename_sb.buf,
					file_it->revision.buf,
					file_basename_sb.buf);
		file_it++;
	}

	cvs_write(cvs, WR_NOFLUSH,	"Directory .\n"
					"%s/%s\n",
					cvs->repo_path, cvs->module);

	ret = cvs_write(cvs, WR_FLUSH, "tag\n");

	if (ret == -1)
		die("cvs tag failed");

	strbuf_grow(&reply, CVS_MAX_LINE);

	while (1) {
		ret = cvs_getreply_firstmatch(cvs, &reply, "M ");
		if (ret == -1) {
			break;
		}
		else if (ret == 1) { /* ok from server */
			rc = 0;
			break;
		}

		tracef("CVS M: %s", reply.buf);
	}

	strbuf_release(&file_basename_sb);
	strbuf_release(&dir_repo_relative_sb);
	strbuf_release(&dir_sb);
	strbuf_release(&reply);
	return rc;
}
