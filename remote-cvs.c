#include "cache.h"
#include "remote.h"
#include "strbuf.h"
#include "url.h"
#include "refs.h"
#include "exec_cmd.h"
#include "run-command.h"
#include "vcs-cvs/cvs-client.h"
#include "vcs-cvs/meta-store.h"
#include "vcs-cvs/aggregator.h"
#include "vcs-cvs/trace-utils.h"
#include "vcs-cvs/ident-utils.h"
#include "notes.h"
#include "argv-array.h"
#include "commit.h"
#include "progress.h"
#include "diff.h"
#include "dir.h"
#include "string-list.h"
#include "blob.h"

/*
 * TODO:
 * -/+ skip dead file addition to HEAD branch
 * - depth / import time
 * -/+ check that metadata correspond to ls-tree files (all files have rev, but no extra)
 * - authors ref/note
 * -/+ safe cancelation point + update time for branch OR ref cmp
 * - delay cvs connect until needed
 * - support options (progress, verbosity, dry-run)
 * - save CVS error and info messages in buffer
 * -/+ sort rlog, avoid extra commits splits done same seconds
 * -/+ validation code: rls -R -d -e -D 'Apr 27 12:37:19 2013'
 *
 * - branch/tags import/ignore list
 * - don't import changes from last N minutes
 * - save next update dates to special ref
 *
 * KNOWN PITFALLS:
 * - CVS has no symlinks support
 * - CVS file permittions history is not tracked (CVS have that feature commented)
 * - CVS file permittions cannot be changed for existing files (even if deleted first)
 *
 * [cvshelper]
 *	ignoreModeChange - bool
 *	fileMemoryLimit - long
 *	pushNoRefsUpdate - bool
 *	verifyImport - bool
 *	trace - path
 *	cvsProtoTrace - path
 *	remoteHelperTrace - path
 *	requireAuthorConvert - bool
 *	dumbRlog - bool
 *	aggregatorFuzzTime - long
 * hooks:
 *	- conversion of CVS user ids which are not in cvs-authors cache file
 *	- input:
 *	    <userid> as argument
 *	- output expected:
 *	    full user ident in form "user name <email>" on stdout
 *	cvs-author-convert <userid>
 *	cvs-import-commit
 *	cvs-export-commit
 * [filter "loose-blob"]
 *  remote = cvs
 *  smudge = get-loose-blob
 *  clean = hash-loose-blob
 *  required
 *
 */

static const char trace_key[] = "GIT_TRACE_CVS_HELPER";
static const char trace_proto[] = "RHELPER";
static const char dump_cvs_commit[] = "GIT_DUMP_PATCHSETS";
/*
 * FIXME:
 */
unsigned long fileMemoryLimit = 2 * 1024 * 1024 * 1024L; //50*1024*1024; /* 50m */
int dumb_rlog = 0;
time_t fuzz_time = 2*60*60; // 2 hours

static int depth = 0;
static int verbosity = 0;
static int show_progress = 1;
static int followtags = 0;
static int dry_run = 0;
static int initial_import = 0;

static int no_refs_update_on_push = 0;
static int ignore_mode_change = 0;
static int verify_import = 0;
static int require_author_convert = 0;
static int update_tags = 0;
static struct progress *progress_state;

static int markid = 0;
static int revisions_all_branches_total = 0;
static int revisions_all_branches_fetched = 0;
static int skipped = 0;
static time_t import_start_time = 0;
//static off_t fetched_total_size = 0;
static const char *single_commit_push = NULL;

static const char *cvsmodule = NULL;
static const char *cvsroot = NULL;
static struct cvs_transport *cvs = NULL;
static struct strbuf push_error_sb = STRBUF_INIT;

#define BRANCH_NOT_IMPORTED ((void*)0)
#define BRANCH_IMPORTED     ((void*)1)
#define BRANCH_IS_TAG       ((void*)2)
static struct string_list cvs_branch_list = STRING_LIST_INIT_DUP;
static struct string_list cvs_tag_list = STRING_LIST_INIT_DUP;
static struct string_list *import_branch_list = NULL;
static struct dir_struct *exclude_dir = NULL;
static struct dir_struct *lfsblob_dir = NULL;
static const char *lfsblob_tag_ref_prefix = "refs/lfs-blobs/";
static struct strbuf lfsblob_gitattr_sb = STRBUF_INIT;

static const char import_commit_edit[] = "IMPORT_COMMIT_EDIT";
static const char export_commit_edit[] = "EXPORT_COMMIT_EDIT";
static int have_import_hook = 0;
static int have_export_hook = 0;

static int cmd_capabilities(const char *line);
static int cmd_option(const char *line);
static int cmd_list(const char *line);
static int cmd_list_for_push(const char *line);
static int cmd_batch_import(struct string_list *list);
static int cmd_batch_push(struct string_list *list);
static int import_branch_by_name(const char *branch_name);
static int validate_commit_meta_by_tree(const char *ref, struct hash_table *revision_meta_hash);

typedef int (*input_command_handler)(const char *);
typedef int (*input_batch_command_handler)(struct string_list *);
struct input_command_entry {
	const char *name;
	input_command_handler fn;
	input_batch_command_handler batch_fn;
	unsigned char batchable;	/* whether the command starts or is part of a batch */
};

static const struct input_command_entry input_command_list[] = {
	{ "capabilities", cmd_capabilities, NULL, 0 },
	{ "option", cmd_option, NULL, 0 },
	{ "import", NULL, cmd_batch_import, 1 },
	{ "bidi-import", NULL, NULL, 0 },
	{ "push", NULL, cmd_batch_push, 1 },
	// `list for-push` should go before `list`, or later would always be run
	{ "list for-push", cmd_list_for_push, NULL, 0 },
	{ "list", cmd_list, NULL, 0 },
	{ NULL, NULL, NULL, 0 }
};

static ssize_t helper_printf(const char *fmt, ...) __attribute__((format (printf, 1, 2)));

static ssize_t helper_printf(const char *fmt, ...)
{
	va_list args;
	ssize_t written;

	va_start(args, fmt);
	written = vprintf(fmt, args);
	va_end(args);

	if (trace_want(trace_key)) {
		struct strbuf tracebuf = STRBUF_INIT;
		va_start(args, fmt);
		strbuf_vaddf(&tracebuf, fmt, args);
		va_end(args);
		proto_trace(tracebuf.buf, tracebuf.len, OUT);
		strbuf_release(&tracebuf);
	}


	return written;
}

static ssize_t helper_write(const char *buf, size_t len)
{
	ssize_t written;
	proto_trace(buf, len, OUT_BLOB);

	written = fwrite(buf, 1, len, stdout);

	return written;
}

static void helper_flush()
{
	fflush(stdout);
	proto_trace_flush();
}

static int helper_strbuf_getline(struct strbuf *sb)
{
	if (strbuf_getwholeline(sb, stdin, '\n')) {
		if (ferror(stdin))
			die("Error reading command stream");
		else
			die("Unexpected end of command stream");
	}

	proto_trace(sb->buf, sb->len, IN);

	if (sb->buf[sb->len-1] == '\n')
		strbuf_setlen(sb, sb->len-1);

	return 0;
}

static const char *gettext_after(const char *str, const char *what)
{
	size_t len = strlen(what);

	if (!strncmp(str, what, len)) {
		return str + len;
	}
	return NULL;
}

static int cmd_capabilities(const char *line)
{
	helper_printf("import\n");
	helper_printf("bidi-import\n");
	helper_printf("push\n");
	helper_printf("option\n");
	helper_printf("refspec refs/heads/*:%s*\n", get_private_ref_prefix());
	helper_printf("refspec refs/tags/*:%s*\n", get_private_tags_ref_prefix());
	helper_printf("\n");
	helper_flush();
	return 0;
}

static int cmd_option(const char *line)
{
	const char *opt;
	const char *val;

	opt = gettext_after(line, "option ");
	if (!opt)
		die("Malformed option request");

	if ((val = gettext_after(opt, "depth "))) {
		depth = atoi(val);
	}
	else if ((val = gettext_after(opt, "verbosity "))) {
		verbosity = atoi(val);
	}
	else if ((val = gettext_after(opt, "progress "))) {
		if (!strcmp(val, "true"))
			show_progress = 1;
	}
	else if ((val = gettext_after(opt, "dry-run "))) {
		if (!strcmp(val, "true"))
			dry_run = 1;
	}
	else if ((val = gettext_after(opt, "followtags "))) {
		if (!strcmp(val, "true"))
			followtags = 1;
	}
	else {
		helper_printf("unsupported\n");
		helper_flush();
		return 0;
	}
	helper_printf("ok\n");
	helper_flush();
	return 0;
}

static void init_cvs_import_exclude()
{
	const char *cvs_exclude_path;

	if (exclude_dir)
		return;

	exclude_dir = xcalloc(1, sizeof(*exclude_dir));

	//exclude_dir->exclude_per_dir = ".gitignore";
	cvs_exclude_path = git_path("info/cvs-exclude");
	if (!access_or_warn(cvs_exclude_path, R_OK, 0))
		add_excludes_from_file(exclude_dir, cvs_exclude_path);

	cvs_exclude_path = getenv("GIT_CVS_IMPORT_EXCLUDE");
	if (cvs_exclude_path) {
		if (access(cvs_exclude_path, R_OK))
			die("cannot access %s specified as GIT_CVS_IMPORT_EXCLUDE",
			    cvs_exclude_path);
		add_excludes_from_file(exclude_dir, cvs_exclude_path);
	}
}

static void free_cvs_import_exclude()
{
	if (!exclude_dir)
		return;

	clear_directory(exclude_dir);
	free(exclude_dir);
}

static int is_cvs_import_excluded_path(const char *path)
{
	int dtype = DT_UNKNOWN;

	if (!exclude_dir)
		init_cvs_import_exclude();

	return is_excluded(exclude_dir, path, &dtype);
}

static int *make_lfsblob_gitattr_filter()
{
	int exfile;
	for (exfile = 0; exfile < lfsblob_dir->exclude_list_group[EXC_FILE].nr; exfile++) {
		struct exclude_list *el = &lfsblob_dir->exclude_list_group[2].el[exfile];
		int ptrn;
		for (ptrn = 0; ptrn < el->nr; ptrn++)
			strbuf_addf(&lfsblob_gitattr_sb,
					"%s filter=lfs diff=lfs merge=lfs -crlf\n",
					el->excludes[ptrn]->pattern);
	}

	return 0;
}

static void init_cvs_lfsblob_filter()
{
	const char *cvs_lfsblob_path;

	if (lfsblob_dir)
		return;

	lfsblob_dir = xcalloc(1, sizeof(*lfsblob_dir));

	cvs_lfsblob_path = git_path("info/cvs-lfsblob");
	if (!access_or_warn(cvs_lfsblob_path, R_OK, 0))
		add_excludes_from_file(lfsblob_dir, cvs_lfsblob_path);

	cvs_lfsblob_path = getenv("GIT_CVS_IMPORT_LFS_FILTER");
	if (cvs_lfsblob_path) {
		if (access(cvs_lfsblob_path, R_OK))
			die("cannot access %s specified as GIT_CVS_IMPORT_LFS_FILTER",
			    cvs_lfsblob_path);
		add_excludes_from_file(lfsblob_dir, cvs_lfsblob_path);
	}

	make_lfsblob_gitattr_filter();
}

static void free_cvs_lfsblob_filter()
{
	if (!lfsblob_dir)
		return;

	clear_directory(lfsblob_dir);
	free(lfsblob_dir);
}

static int is_cvs_lfsblob_path(const char *path)
{
	int dtype = DT_UNKNOWN;

	if (!lfsblob_dir)
		init_cvs_lfsblob_filter();

	return is_excluded(lfsblob_dir, path, &dtype);
}

char *sha256_to_hex(const unsigned char *sha256)
{
	static int bufno;
	static char hexbuffer[4][git_SHA256_DIGEST_LENGTH * 2 + 1];
	static const char hex[] = "0123456789abcdef";
	char *buffer = hexbuffer[3 & ++bufno], *buf = buffer;
	int i;

	for (i = 0; i < git_SHA256_DIGEST_LENGTH; i++) {
		unsigned int val = *sha256++;
		*buf++ = hex[val >> 4];
		*buf++ = hex[val & 0xf];
	}
	*buf = '\0';

	return buffer;
}

/*
 * git lfs client has a bug, it tries to minic git concept but actually creates
 * files with full sha256 name, despite using first 2 bytes as directries
 */
char *get_lfs_blob_path_client(const unsigned char *sha256)
{
	return git_path("lfs/objects/%02hhx/%02hhx/%s", sha256[0], sha256[1], sha256_to_hex(sha256)/* + 4*/);
}

char *get_lfs_blob_path_server(const unsigned char *sha256)
{
	return git_path("lfs/server/%02hhx/%02hhx/%s", sha256[0], sha256[1], sha256_to_hex(sha256) + 4);
}

static inline void sha256hashcpy(unsigned char *sha_dst, const unsigned char *sha_src)
{
	memcpy(sha_dst, sha_src, git_SHA256_DIGEST_LENGTH);
}

void sha256_buf(const void *buf, unsigned long len, unsigned char *returnsha256)
{
	git_SHA256_CTX sha256;
	git_SHA256_Init(&sha256);
	git_SHA256_Update(&sha256, buf, len);
	git_SHA256_Final(returnsha256, &sha256);
}

int has_sha256_lfs_file(const unsigned char *sha256)
{
	struct stat st;
	if (stat(get_lfs_blob_path_client(sha256), &st))
		return 0;
	return 1;
}

static void create_directories(const char *path)
{
	int path_len = strlen(path);
	char *buf = xmalloc(path_len + 1);
	int len = 0;

	while (len < path_len) {
		do {
			buf[len] = path[len];
			len++;
		} while (len < path_len && path[len] != '/');
		if (len >= path_len)
			break;
		buf[len] = 0;

		if (mkdir(buf, 0777)) {
			if (errno == EEXIST)
				continue;
			die_errno("cannot create directory at '%s'", buf);
		}
	}
	free(buf);
}

int store_lfs_blob_file(const void *buf, unsigned long len, unsigned char *sha256)
{
	char *path = get_lfs_blob_path_client(sha256);
	ssize_t written;
	int fd;

	create_directories(path);
	fd = open(path, O_CREAT | O_WRONLY, 0666);
	if (fd < 0)
		die (_("Could not open '%s' for writing."), path);

	// create hard link for easy importing of lfs blobs to server
	char *servpath = get_lfs_blob_path_server(sha256);
	create_directories(servpath);
	link(path, servpath);

	written = write_in_full(fd, buf, len);
	close(fd);
	return written == len ? 0 : 1;
}

int write_sha256_lfs_file(const void *buf, unsigned long len, unsigned char *sha256)
{
	sha256_buf(buf, len, sha256);
	if (has_sha256_lfs_file(sha256))
		return 0;

	return store_lfs_blob_file(buf, len, sha256);
}

static const char *get_import_time_estimation()
{
	static const char *now = " 00:00, ";
	static struct strbuf eta_sb = STRBUF_INIT;
	time_t eta = time(NULL) - import_start_time;
	struct tm tm_eta;

	if (!eta)
		return now;

	eta = (double)eta / (double)revisions_all_branches_fetched *
		(double)(revisions_all_branches_total - revisions_all_branches_fetched);

	if (!eta)
		return now;

	memset(&tm_eta, 0, sizeof(tm_eta));
	gmtime_r(&eta, &tm_eta);

	strbuf_reset(&eta_sb);
	if (tm_eta.tm_year - 70) // year since 1900, 1970 is unix time start
		strbuf_addf(&eta_sb, " %d years, ", tm_eta.tm_year - 70);
	if (tm_eta.tm_mon)
		strbuf_addf(&eta_sb, " %d months, ", tm_eta.tm_mon);
	if (tm_eta.tm_mday - 1)
		strbuf_addf(&eta_sb, " %d days, ", tm_eta.tm_mday - 1);
	if (tm_eta.tm_hour)
		strbuf_addf(&eta_sb, " %d hours, ", tm_eta.tm_hour);
	if (tm_eta.tm_min)
		strbuf_addf(&eta_sb, " %d min, ", tm_eta.tm_min);
	if (tm_eta.tm_sec)
		strbuf_addf(&eta_sb, " %d sec, ", tm_eta.tm_sec);

	return eta_sb.buf;
}

static int fast_export_blob(void *buf, size_t size)
{
	/*
	'blob' LF
	mark?
	'data' SP <count> LF
	<raw> LF?
	*/

	markid++;
	helper_printf("blob\n");
	helper_printf("mark :%d\n", markid);
	helper_printf("data %zu\n", size);
	helper_write(buf, size);
	helper_printf("\n");

	return markid;
}

static int fast_export_revision_cb(void *ptr, void *data)
{
	struct cvs_revision *rev = ptr;
	struct string_list *lfsblob_list = data;

	if (rev->isdead) {
		helper_printf("D %s\n", rev->path);
		return 0;
	}

	if (!rev->mark)
		die("No mark during fast_export_revision_by_mark");

	if (is_cvs_lfsblob_path(rev->path)) {
		struct strbuf lfsblob_sb = STRBUF_INIT;
		/*
		 * FIXME: cache and do not read object from git to generate lfs pointer
		 */
		unsigned long size;
		enum object_type type;
		void *buf;
		unsigned char sha256[git_SHA256_DIGEST_LENGTH];
		unsigned char sha1[20];

		if (rev->mark[0] == ':')
			die("fast_export_revision: mark for loose-blob is not sha1");

		get_sha1_hex(rev->mark, sha1);
		buf = read_sha1_file(sha1, &type, &size);
		if (!buf)
			die("fast_export_revision: cannot read git lfs object by sha1: %s", rev->mark);
		sha256_buf(buf, size, sha256);

		strbuf_addf(&lfsblob_sb, "version https://git-lfs.github.com/spec/v1\n"
								"oid sha256:%s\n"
								"size %lu\n",
								sha256_to_hex(sha256), size);
		helper_printf("M 100%.3o inline %s\n", rev->isexec ? 0755 : 0644, rev->path);
		helper_printf("data %zu\n", lfsblob_sb.len);
		helper_write(lfsblob_sb.buf, lfsblob_sb.len);
		helper_printf("\n");
		strbuf_release(&lfsblob_sb);
		string_list_append(lfsblob_list, rev->mark);
	}
	else {
		helper_printf("M 100%.3o %s %s\n", rev->isexec ? 0755 : 0644, rev->mark, rev->path);
	}
	return 0;
}

static int cvs_checkout_rev_retry(struct cvs_transport *cvs, const char *path, const char *revision, struct cvsfile *file)
{
	if (!cvs_checkout_rev(cvs, path, revision, file))
		return 0;

	cvs_terminate(cvs);
	cvs = cvs_connect(cvsroot, cvsmodule);
	if (!cvs)
		die("Cannot checkout file %s rev %s. Cannot reconnect to cvs server.", path, revision);
	return cvs_checkout_rev(cvs, path, revision, file);
}

static int fetch_revision_cb(void *ptr, void *data)
{
	static struct cvsfile file = CVSFILE_INIT;
	struct cvs_revision *rev = ptr;
	char *cached_sha1;
	struct strbuf mark_sb = STRBUF_INIT;
	int isexec;
	int rc;

	if (rev->mark)
		return 0;

	revisions_all_branches_fetched++;
	tracef("checkout [%d/%d] (%.2lf%%) all branches,%sETA] %s %s",
			revisions_all_branches_fetched,
			revisions_all_branches_total,
			(double)revisions_all_branches_fetched/(double)revisions_all_branches_total*100.,
			get_import_time_estimation(),
			rev->path, rev->revision);

	if (rev->isdead) {
		tracef(" (not fetched) dead");
		return 0;
	}

	cached_sha1 = revision_cache_lookup(rev->path, rev->revision, &isexec);
	if (cached_sha1) {
		rev->isexec = isexec;
		rev->mark = xstrdup(cached_sha1);
		tracef(" (fetched from revision cache) isexec %u sha1 %s", isexec, cached_sha1);
		return 0;
	}

	rc = cvs_checkout_rev_retry(cvs, rev->path, rev->revision, &file);
	if (rc == -1)
		die("Cannot checkout file %s rev %s", rev->path, rev->revision);

	if (show_progress) {
		display_progress(progress_state, revisions_all_branches_fetched);
		display_throughput(progress_state, cvs_read_total + cvs_written_total);
	}

	if (file.isdead) {
		rev->isdead = 1;
		tracef(" (fetched) dead");
		return 0;
	}

	if (file.iscached)
		tracef(" (fetched from cache) isexec %u size %zu", file.isexec, file.file.len);
	else
		tracef(" mode %.3o size %zu", file.mode, file.file.len);

	rev->isexec = file.isexec;
	if (is_cvs_lfsblob_path(rev->path)) {
		unsigned char sha1[20];
		unsigned char sha256[git_SHA256_DIGEST_LENGTH];
		//fast_export_blob(file.file.buf, file.file.len);
		//hash_sha1_file(file.file.buf, file.file.len, blob_type, sha1);
		write_sha1_file(file.file.buf, file.file.len, blob_type, sha1);
		strbuf_addf(&mark_sb, "%s", sha1_to_hex(sha1));

		write_sha256_lfs_file(file.file.buf, file.file.len, sha256);
		tracef("written as git lfs file: %s %s - %s", rev->path, rev->revision, sha256_to_hex(sha256));
	}
	else {
		strbuf_addf(&mark_sb, ":%d", fast_export_blob(file.file.buf, file.file.len));
	}
	rev->mark = strbuf_detach(&mark_sb, NULL);
	return 0;
}

static int cache_revision_cb(void *ptr, void *data)
{
	struct cvs_revision *rev = ptr;
	struct strbuf lsbuf = STRBUF_INIT;

	if (rev->isdead)
		return 0;

	if (is_cvs_lfsblob_path(rev->path)) {
		if (rev->mark[0] == ':')
			die("cache_revision: mark for loose-blob is not sha1");
		add_revision_cache_entry(rev->path, rev->revision, rev->isexec, rev->mark);
		return 0;
	}

	helper_printf("ls \"%s\"\n", rev->path);
	helper_flush();
	helper_strbuf_getline(&lsbuf);

	/*
	 * 40 sha + 6 file mode + 6 ' blob '
	 */
	if (lsbuf.len < 52 || strncmp(lsbuf.buf + 6 /*mode*/, " blob ", 6))
		die("unexpected fast-import ls reply: %s", lsbuf.buf);

	strbuf_setlen(&lsbuf, 52);
	add_revision_cache_entry(rev->path, rev->revision, rev->isexec, lsbuf.buf + 12);
	strbuf_release(&lsbuf);
	return 0;
}

static int fast_export_lfsblob_tag(struct string_list_item *li, void *date)
{
	unsigned char sha1[20];
	struct strbuf lfsblob_tag_ref_sb = STRBUF_INIT;

	strbuf_addf(&lfsblob_tag_ref_sb, "%s%s", lfsblob_tag_ref_prefix, li->string);
	get_sha1_hex(li->string, sha1);

	update_ref("tagging lfs blob", lfsblob_tag_ref_sb.buf, sha1, NULL, 0, DIE_ON_ERR);
	/*
	 * fast-import does not support blobs tagging
	 *
	helper_printf("reset %s%s\n", lfsblob_tag_ref_prefix, li->string);
	helper_printf("from %s\n", li->string);
	 */
	strbuf_release(&lfsblob_tag_ref_sb);
	return 0;
}

static int fast_export_lfsblob_gitattributes_filter()
{
	if (!lfsblob_gitattr_sb.len)
		return 0;

	helper_printf("M 100644 inline .gitattributes\n");
	helper_printf("data %zu\n", lfsblob_gitattr_sb.len);
	helper_write(lfsblob_gitattr_sb.buf, lfsblob_gitattr_sb.len);
	return 0;
}

static int run_import_hook(struct strbuf *author_sb, struct strbuf *committer_sb, struct strbuf *commit_msg_sb)
{
	struct strbuf commit = STRBUF_INIT;
	FILE *fp;
	int rc;

	strbuf_addf(&commit, "%s\n%s\n\n%s", author_sb->buf, committer_sb->buf, commit_msg_sb->buf);

	fp = fopen(git_path(import_commit_edit), "w");
	if (fp == NULL)
		die_errno(_("could not open '%s'"), git_path(import_commit_edit));

	if (fwrite(commit.buf, 1, commit.len, fp) < commit.len)
		die_errno("could not write %s", import_commit_edit);
	fclose(fp);

	rc = run_hook(NULL, "cvs-import-commit", git_path(import_commit_edit), NULL);
	if (rc)
		die("cvs-import-commit hook rc %d, aborting import", rc);

	fp = fopen(git_path(import_commit_edit), "r");
	if (fp == NULL)
		die_errno(_("could not open '%s'"), git_path(import_commit_edit));

	if (strbuf_getline(author_sb, fp, '\n'))
		die("could not read %s", git_path(import_commit_edit));

	if (strbuf_getline(committer_sb, fp, '\n'))
		die("could not read %s", git_path(import_commit_edit));

	/*
	 * TODO: verify author/committer lines?
	 */

	strbuf_reset(commit_msg_sb);
	if (strbuf_fread_full(commit_msg_sb, fp, 0) == -1)
		die("could not read %s", git_path(import_commit_edit));
	fclose(fp);

	strbuf_release(&commit);
	return 0;
}

static int fast_export_cvs_commit(const char *branch_name, struct cvs_commit *ps, const char *parent_mark)
{
	const char *author_ident;
	struct strbuf author_sb = STRBUF_INIT;
	struct strbuf committer_sb = STRBUF_INIT;
	struct strbuf commit_msg_sb = STRBUF_INIT;
	struct string_list lfsblob_list = STRING_LIST_INIT_NODUP;

	/*
	'commit' SP <ref> LF
	mark?
	('author' (SP <name>)? SP LT <email> GT SP <when> LF)?
	'committer' (SP <name>)? SP LT <email> GT SP <when> LF
	data
	('from' SP <committish> LF)?
	('merge' SP <committish> LF)?
	(filemodify | filedelete | filecopy | filerename | filedeleteall | notemodify)*
	LF?
	*/

	author_ident = author_convert(ps->author);
	if (require_author_convert && !author_ident)
		die("failed to resolve cvs userid %s", ps->author);

	if (!author_ident) {
		strbuf_addf(&author_sb, "author %s <unknown> %ld +0000", ps->author, ps->timestamp);
		strbuf_addf(&committer_sb, "committer %s <unknown> %ld +0000", ps->author, ps->timestamp_last);
	}
	else {
		strbuf_addf(&author_sb, "author %s %ld +0000", author_ident, ps->timestamp);
		strbuf_addf(&committer_sb, "committer %s %ld +0000", author_ident, ps->timestamp_last);
	}
	strbuf_addstr(&commit_msg_sb, ps->msg);

	if (have_import_hook)
		run_import_hook(&author_sb, &committer_sb, &commit_msg_sb);

	for_each_hash(ps->revision_hash, fetch_revision_cb, NULL);

	markid++;
	helper_printf("commit %s%s\n", get_private_ref_prefix(), branch_name);
	helper_printf("mark :%d\n", markid);
	helper_printf("%s\n", author_sb.buf);
	helper_printf("%s\n", committer_sb.buf);
	helper_printf("data %zu\n", commit_msg_sb.len);
	helper_printf("%s\n", commit_msg_sb.buf);

	if (parent_mark)
		helper_printf("from %s\n", parent_mark);
	for_each_hash(ps->revision_hash, fast_export_revision_cb, &lfsblob_list);
	if (lfsblob_list.nr)
		fast_export_lfsblob_gitattributes_filter();
	for_each_hash(ps->revision_hash, cache_revision_cb, NULL);
	for_each_string_list(&lfsblob_list, fast_export_lfsblob_tag, NULL);
	helper_flush();

	string_list_clear(&lfsblob_list, 0);
	strbuf_release(&author_sb);
	strbuf_release(&committer_sb);
	strbuf_release(&commit_msg_sb);
	return markid;
}

static int fast_export_revision_meta_cb(void *ptr, void *data)
{
	struct cvs_revision *rev = ptr;
	struct strbuf *sb = data;

	format_add_meta_line(sb, rev);
	return 0;
}

static int print_revision_changes_cb(void *ptr, void *data)
{
	struct cvs_revision *rev = ptr;

	if (!rev->isdead)
		helper_printf("updated %s %s\n", rev->revision, rev->path);
	else
		helper_printf("deleted %s %s\n", rev->revision, rev->path);
	//helper_printf("%s:%c:%s\n", rev->revision, rev->isdead ? '-' : '+', rev->path);
	return 0;
}

static int fast_export_commit_meta(const char *branch_name,
				int istag,
				struct hash_table *meta,
				struct hash_table *changes_hash,
				time_t timestamp,
				const char *commit_mark,
				const char *parent_mark)
{
	struct strbuf sb = STRBUF_INIT;

	markid++;
	helper_printf("commit %s%s\n",
			istag ? get_meta_tags_ref_prefix() : get_meta_ref_prefix(),
			branch_name);
	helper_printf("mark :%d\n", markid);
	helper_printf("committer remote-cvs <unknown> %ld +0000\n", timestamp);
	helper_printf("data <<EOM\n");
	helper_printf("cvs meta update\n");
	if (changes_hash)
		for_each_hash(changes_hash, print_revision_changes_cb, NULL);
	helper_printf("EOM\n");
	if (parent_mark)
		helper_printf("from %s\n", parent_mark);
	helper_printf("N inline %s\n", commit_mark);
	helper_printf("data <<EON\n");
	if (timestamp)
		helper_printf("UPDATE:%ld\n", timestamp);
	helper_printf("--\n");
	for_each_hash(meta, fast_export_revision_meta_cb, &sb);
	helper_printf("%s", sb.buf);
	helper_printf("EON\n");
	//helper_printf("\n");
	helper_flush();

	strbuf_release(&sb);
	return markid;
}

static int update_revision_hash(void *ptr, void *data)
{
	struct cvs_revision *rev = ptr;
	struct hash_table *meta = data;

	unsigned int hash;
	void **pos;

	hash = hash_path(rev->path);
	pos = insert_hash(hash, rev, meta);
	if (pos) {
		struct cvs_revision *prev = *pos;

		if (strcmp(rev->path, prev->path))
			die("file path hash collision");

		*pos = rev;
	}
	return 0;
}

static void on_file_checkout_cb(struct cvsfile *file, void *data)
{
	struct hash_table *meta_revision_hash = data;
	struct strbuf mark_sb = STRBUF_INIT;
	int mark;

	revisions_all_branches_total++;
	revisions_all_branches_fetched++;
	tracef("on checkout [%d/%d] (%.2lf%%) all branches,%sETA] %s %s",
			revisions_all_branches_fetched,
			revisions_all_branches_total,
			(double)revisions_all_branches_fetched/(double)revisions_all_branches_total*100.,
			get_import_time_estimation(),
			file->path.buf, file->revision.buf);

	if (show_progress) {
		display_progress(progress_state, revisions_all_branches_fetched);
		display_throughput(progress_state, cvs_read_total + cvs_written_total);
	}

	if (is_cvs_import_excluded_path(file->path.buf)) {
		tracef("%s ignored during import according to cvs-exclude", file->path.buf);
		return;
	}

	/*
	 * FIXME: support files on disk
	 */
	if (!file->ismem)
		die("no support for files on disk yet");

	mark = fast_export_blob(file->file.buf, file->file.len);
	strbuf_addf(&mark_sb, ":%d", mark);

	add_cvs_revision_hash(meta_revision_hash, file->path.buf, file->revision.buf,
			      file->timestamp, file->isdead, file->isexec, strbuf_detach(&mark_sb, NULL));
}

static int checkout_branch(const char *branch_name, time_t import_time, struct hash_table *meta_revision_hash)
{
	int rc;

	/*
	 * cvs checkout is broken, it uses command arguments from earilier
	 * commands. New session is needed.
	 */
	struct cvs_transport *cvs_co = cvs_connect(cvsroot, cvsmodule);
	if (!cvs_co)
		return -1;

	rc = cvs_checkout_branch(cvs_co, branch_name, import_time, on_file_checkout_cb, meta_revision_hash);
	if (rc)
		die("cvs checkout of %s date %ld failed", branch_name, import_time);

	return cvs_terminate(cvs_co);
}

static void on_rlist_file_cb(const char *path, const char *revision, time_t timestamp, void *data)
{
	struct hash_table *meta_revision_hash = data;

	if (is_cvs_import_excluded_path(path)) {
		tracef("%s ignored during import according to cvs-exclude", path);
		return;
	}

	add_cvs_revision_hash(meta_revision_hash, path, revision, timestamp, 0, 0, NULL);
}

static int rlist_branch(const char *branch_name, time_t import_time, struct hash_table *meta_revision_hash)
{
	int rc;
	size_t written = cvs->written;
	rc = cvs_rls(cvs, branch_name, 0, import_time, on_rlist_file_cb, meta_revision_hash);
	if (rc)
		die("cvs rls of %s date %ld failed", branch_name, import_time);

	revisions_all_branches_total += meta_revision_hash->nr;

	/*
	 * FIXME: rls somehow breaks all server connections (even in separate
	 * processes), in a way single module checkouts starting to fail
	 */
	if (written != cvs->written) { // a hack to avoid cvs reconnection if rls was read from cache
		cvs_terminate(cvs);
		cvs = cvs_connect(cvsroot, cvsmodule);
		if (!cvs)
			return -1;
	}
	return rc;
}

static int fetch_branch_meta(const char *branch_name, time_t import_time, struct hash_table *meta_revision_hash)
{
	if (cvs->has_rls_support)
		return rlist_branch(branch_name, import_time, meta_revision_hash);
	else
		return checkout_branch(branch_name, import_time, meta_revision_hash);
}

static int count_dots(const char *rev)
{
	int dots = 0;

	while (1) {
		rev = strchr(rev, '.');
		if (!rev)
			break;

		dots++;
		rev++;
	}

	return dots;
}

static char *get_cvs_revision_branch(struct cvs_revision *file_meta)
{
	return cvs_get_rev_branch(cvs, file_meta->path, file_meta->revision);
}

struct find_rev_data {
	struct cvs_revision *file_meta;
	int dots;
};
static int find_longest_rev(void *ptr, void *data)
{
	struct cvs_revision *rev_meta = ptr;
	struct find_rev_data *find_rev_data = data;
	int dots;

	dots = count_dots(rev_meta->revision);
	if (dots > find_rev_data->dots) {
		find_rev_data->dots = dots;
		find_rev_data->file_meta = rev_meta;
	}

	return 0;
}

/*
 * FIXME: longest revision is not always parent
 */
static char *find_parent_branch(const char *branch_name, struct hash_table *meta_revision_hash)
{
	struct find_rev_data find_rev_data = { NULL, 0 };
	for_each_hash(meta_revision_hash, find_longest_rev, &find_rev_data);


	if (find_rev_data.dots == 0)
		die("longest revision is 0");

	if (find_rev_data.dots == 1)
		return xstrdup("HEAD");

	return get_cvs_revision_branch(find_rev_data.file_meta);
}

static int compare_commit_meta(unsigned char sha1[20], const char *meta_ref, struct hash_table *meta_revision_hash)
{
	struct cvs_revision *file_meta;
	char *buf;
	char *p;
	char *revision;
	char *path;
	char *attr;
	unsigned long size;
	int rev_mismatches = 0;
	int isdead;

	buf = read_note_of(sha1, meta_ref, &size);
	if (!buf)
		return -1;

	p = buf;
	while ((p = parse_meta_line(buf, size, &revision, &path, &attr, p))) {
		if (strcmp(revision, "--") == 0)
			break;
	}

	while ((p = parse_meta_line(buf, size, &revision, &path, &attr, p))) {
		if (!path || !attr)
			die("malformed metadata: %s:%s:%s", revision, attr, path);
		isdead = !!strstr(attr, "dead");

		file_meta = lookup_hash(hash_path(path), meta_revision_hash);
		if (!file_meta && isdead)
			continue;

		if (!file_meta ||
		    strcmp(file_meta->revision, revision))
			rev_mismatches++;
	}

	free(buf);
	return rev_mismatches;
}

static const char *find_branch_fork_point(const char *parent_branch_name, time_t time, struct hash_table *meta_revision_hash)
{
	unsigned char sha1[20];
	struct commit *commit;
	struct strbuf branch_ref = STRBUF_INIT;
	struct strbuf cvs_branch_ref = STRBUF_INIT;
	const char *commit_ref = NULL;
	int rev_mismatches_min = INT_MAX;
	int rev_mismatches;

	save_commit_buffer = 0;
	if (!time)
		time = -1;

	strbuf_addf(&branch_ref, "%s%s", get_private_ref_prefix(), parent_branch_name);
	strbuf_addf(&cvs_branch_ref, "%s%s", get_meta_ref_prefix(), parent_branch_name);

	if (get_sha1_commit(branch_ref.buf, sha1))
		die("cannot find last commit on branch ref %s", branch_ref.buf);

	commit = lookup_commit(sha1);

	for (;;) {
		if (parse_commit(commit))
			die("cannot parse commit %s", sha1_to_hex(commit->object.sha1));
		tracef("find_branch_fork_point: commit: %s date: %s commit: %p",
			sha1_to_hex(commit->object.sha1), show_date(commit->date, 0, DATE_NORMAL), commit);

		if (commit->date <= time) {
			rev_mismatches = compare_commit_meta(commit->object.sha1, cvs_branch_ref.buf, meta_revision_hash);
			tracef("rev_mismatches: %d", rev_mismatches);
			if (rev_mismatches == -1) {
				/*
				 * TODO: compare_commit_meta return -1 if no
				 * metadata note available for commit. Is this
				 * an error?
				 * commit_ref = NULL;
				 */
				break;
			}

			if (!rev_mismatches) {
				tracef("find_branch_fork_point - perfect match");
				commit_ref = sha1_to_hex(commit->object.sha1);
				break;
			}

			if (rev_mismatches_min < rev_mismatches)
				break;

			if (rev_mismatches_min > rev_mismatches) {
				rev_mismatches_min = rev_mismatches;
				commit_ref = sha1_to_hex(commit->object.sha1);
			}
		}

		if (!commit->parents)
			break;
		commit = commit->parents->item;
	}

	strbuf_release(&branch_ref);
	strbuf_release(&cvs_branch_ref);
	return commit_ref;
}

/*const int maxrevlen = 32;

int rev2array(const char *ver, int *arr, int *arrlen)
{
	const char *c = ver;
	int len = 0;
	int digit = 0;

	while (true) {
		switch (*c) {
			case '\0':
				arr[len++] = digit;
				*arrlen = len;
				return 0;
			case '.':
				arr[len++] = digit;
				if (len >= maxrevlen)
					return -1;
				digit = 0;
				break;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':
				digit *= 10;
				digit += *c - '0';
				break;
			default:
				return -1;
		}
		c++;
	}
}

int revcmp(const char *ver1, const char *ver2)
{
	if (!strcmp(ver1, ver2))
		return 0;

	int ver1arr[maxrevlen];
	int ver1len;
	int ver2arr[maxrevlen];
	int ver2len;
	int i;

	rev2array(ver1, ver1arr, &ver1len);
	rev2array(ver2, ver2arr, &ver2len);

	int minlen = ver1len < ver2len ? ver1len : ver2len;
	for (i = 0; i < minlen; i++) {
		if (ver1arr[i] == ver2arr[i])
			continue;
		if (ver1arr[i] < ver2arr[i])
			return -1;
		if (ver1arr[i] > ver2arr[i])
			return 1;
	}

	if (ver1len < ver2len)
		return -1;
	else
		return 1;
}


static const char *fork_branch(const char *branch_name, const char *parent_branch_name, time_t time, struct hash_table *meta_revision_hash)
{
	unsigned char sha1[20];
	struct commit *commit;
	struct strbuf branch_ref = STRBUF_INIT;
	struct strbuf cvs_branch_ref = STRBUF_INIT;
	const char *commit_ref = NULL;
	int rev_mismatches_min = INT_MAX;
	int rev_mismatches;

	save_commit_buffer = 0;
	if (!time)
		time = -1;

	strbuf_addf(&branch_ref, "%s%s", get_private_ref_prefix(), parent_branch_name);
	strbuf_addf(&cvs_branch_ref, "%s%s", get_meta_ref_prefix(), parent_branch_name);

	if (get_sha1_commit(branch_ref.buf, sha1))
		die("cannot find last commit on branch ref %s", branch_ref.buf);

	commit = lookup_commit(sha1);

	for (;;) {
		if (parse_commit(commit))
			die("cannot parse commit %s", sha1_to_hex(commit->object.sha1));
		tracef("find_branch_fork_point: commit: %s date: %s commit: %p",
			sha1_to_hex(commit->object.sha1), show_date(commit->date, 0, DATE_NORMAL), commit);

		if (commit->date <= time) {
			rev_mismatches = compare_commit_meta(commit->object.sha1, cvs_branch_ref.buf, meta_revision_hash);
			tracef("rev_mismatches: %d", rev_mismatches);
			if (rev_mismatches == -1) {
				*
				 * TODO: compare_commit_meta return -1 if no
				 * metadata note available for commit. Is this
				 * an error?
				 * commit_ref = NULL;
				 *
				break;
			}

			if (!rev_mismatches) {
				tracef("find_branch_fork_point - perfect match");
				commit_ref = sha1_to_hex(commit->object.sha1);
				break;
			}

			if (rev_mismatches_min < rev_mismatches)
				break;

			if (rev_mismatches_min > rev_mismatches) {
				rev_mismatches_min = rev_mismatches;
				commit_ref = sha1_to_hex(commit->object.sha1);
			}
		}

		if (!commit->parents)
			break;
		commit = commit->parents->item;
	}

	strbuf_release(&branch_ref);
	strbuf_release(&cvs_branch_ref);
	return commit_ref;
}*/

static int fast_export_branch_initial(const char *branch_name,
					int istag,
					struct hash_table *meta_revision_hash,
					time_t date,
					const char *parent_commit_mark,
					const char *parent_branch_name)
{
	struct string_list lfsblob_list = STRING_LIST_INIT_NODUP;
	for_each_hash(meta_revision_hash, fetch_revision_cb, NULL);

	markid++;
	helper_printf("commit %s%s\n",
			istag ? get_private_tags_ref_prefix() : get_private_ref_prefix(),
			branch_name);
	helper_printf("mark :%d\n", markid);
	helper_printf("author git-remote-cvs <none> %ld +0000\n", date);
	helper_printf("committer git-remote-cvs <none> %ld +0000\n", date);
	helper_printf("data <<EON\n");
	helper_printf("initial import of %s: %s\nparent branch: %s\n",
			istag ? "tag" : "branch", branch_name, parent_branch_name);
	helper_printf("EON\n");
	if (parent_commit_mark) {
		helper_printf("from %s\n", parent_commit_mark);
		helper_printf("deleteall\n");
	}
	for_each_hash(meta_revision_hash, fast_export_revision_cb, &lfsblob_list);
	if (lfsblob_list.nr)
		fast_export_lfsblob_gitattributes_filter();
	for_each_hash(meta_revision_hash, cache_revision_cb, NULL);
	for_each_string_list(&lfsblob_list, fast_export_lfsblob_tag, NULL);
	helper_flush();

	string_list_clear(&lfsblob_list, 0);
	return markid;
}

static int find_last_change_time_cb(void *ptr, void *data)
{
	struct cvs_revision *rev = ptr;
	time_t *time_max = data;

	if (rev->timestamp > *time_max)
		*time_max = rev->timestamp;

	return 0;
}

static int do_initial_import(const char *branch_name, int istag, time_t import_time, struct hash_table *revision_hash)
{
	int mark;
	char *parent_branch_name;
	const char *parent_commit;
	struct string_list_item *item;
	struct strbuf commit_mark_sb = STRBUF_INIT;

	if (fetch_branch_meta(branch_name, import_time, revision_hash))
		die("%s checkout failed", branch_name);

	if (is_empty_hash(revision_hash))
		return 0;

	parent_branch_name = find_parent_branch(branch_name, revision_hash);
	if (!parent_branch_name)
		die("Cannot find parent branch for: %s", branch_name);
	tracef("parent branch for: %s is %s", branch_name, parent_branch_name);

	if (!import_time)
		for_each_hash(revision_hash, find_last_change_time_cb, &import_time);
	tracef("import timestamp: %ld", import_time);

	/*
	 * if parent is not updated yet, import parent first
	 */
	item = unsorted_string_list_lookup(import_branch_list, parent_branch_name);
	if (item && item->util == BRANCH_NOT_IMPORTED) {
		tracef("fetching parent first");
		import_branch_by_name(item->string);
		item->util = BRANCH_IMPORTED;
	}

	parent_commit = find_branch_fork_point(parent_branch_name,
						import_time,
						revision_hash);
	tracef("parent commit: %s", parent_commit);

	mark = fast_export_branch_initial(branch_name,
					istag,
					revision_hash,
					import_time,
					parent_commit,
					parent_branch_name);

	strbuf_addf(&commit_mark_sb, ":%d", mark);
	fast_export_commit_meta(branch_name,
				istag,
				revision_hash,
				NULL,
				import_time,
				commit_mark_sb.buf,
				NULL);

	free(parent_branch_name);
	strbuf_release(&commit_mark_sb);
	return mark;
}

static int initial_branch_import(const char *branch_name, struct cvs_branch *cvs_branch)
{
	time_t import_time = find_first_commit_time(cvs_branch);
	if (!import_time)
		die("import time is 0");
	import_time--;
	tracef("import time is %s", show_date(import_time, 0, DATE_RFC2822));

	return do_initial_import(branch_name, 0, import_time, cvs_branch->last_commit_revision_hash);
}

static int initial_empty_branch_import(const char *branch_name)
{
	int mark;
	struct hash_table revision_hash = HASH_TABLE_INIT;

	mark = do_initial_import(branch_name, 0, 0, &revision_hash);
	free_revision_meta(&revision_hash);
	return !mark;
}

static void merge_revision_hash(struct hash_table *meta, struct hash_table *update)
{
	for_each_hash(update, update_revision_hash, meta);
}

static int import_branch_by_name(const char *branch_name)
{
	int mark;
	int rc;
	unsigned char sha1[20];
	struct strbuf commit_mark_sb = STRBUF_INIT;
	struct strbuf meta_mark_sb = STRBUF_INIT;
	struct strbuf branch_ref = STRBUF_INIT;
	struct strbuf branch_private_ref = STRBUF_INIT;
	struct strbuf meta_branch_ref = STRBUF_INIT;
	struct strbuf buf_sb = STRBUF_INIT;
	struct hash_table meta_revision_hash;
	struct string_list_item *li;

	tracef("importing CVS branch %s", branch_name);

	struct cvs_branch *cvs_branch;
	int psnum = 0;
	int pstotal = 0;

	li = unsorted_string_list_lookup(&cvs_branch_list, branch_name);
	if (!li) // && !ref_exists(meta_branch_ref.buf))
		die("Cannot find meta for branch %s\n", branch_name);
	cvs_branch = li->util;

	strbuf_addf(&meta_branch_ref, "%s%s", get_meta_ref_prefix(), branch_name);
	if (!cvs_branch) {
		if (ref_exists(meta_branch_ref.buf))
			die("initial_empty_branch_import of already imported branch %s", branch_name);
		rc = initial_empty_branch_import(branch_name);
		strbuf_release(&meta_branch_ref);
		return rc;
	}

	strbuf_addf(&branch_ref, "%s%s", get_ref_prefix(), branch_name);

	/*
	 * FIXME: support of repositories with no files
	 */
	if (is_empty_hash(cvs_branch->last_commit_revision_hash) &&
	    strcmp(branch_name, "HEAD")) {
		/*
		 * no meta, do cvs checkout
		 */
		mark = initial_branch_import(branch_name, cvs_branch);
		if (mark == -1)
			die("initial_branch_import failed %s", branch_name);
		if (mark > 0)
			strbuf_addf(&commit_mark_sb, ":%d", mark);
	}
	else {
		if (!get_sha1(branch_ref.buf, sha1))
			strbuf_addstr(&commit_mark_sb, sha1_to_hex(sha1));
		if (!get_sha1(meta_branch_ref.buf, sha1))
			strbuf_addstr(&meta_mark_sb, sha1_to_hex(sha1));
	}
	aggregate_cvs_commits(cvs_branch);

	init_hash(&meta_revision_hash);
	merge_revision_hash(&meta_revision_hash, cvs_branch->last_commit_revision_hash);

	cvs_authors_load();

	pstotal = get_cvs_commit_count(cvs_branch);
	struct cvs_commit *ps = cvs_branch->cvs_commit_list->head;
	while (ps) {
		psnum++;
		tracef("-->>------------------");
		tracef("Branch: %s Commit: %d/%d", branch_name, psnum, pstotal);
		print_cvs_commit(ps);
		tracef("--<<------------------");
		mark = fast_export_cvs_commit(branch_name, ps, commit_mark_sb.len ? commit_mark_sb.buf : NULL);
		strbuf_reset(&commit_mark_sb);
		strbuf_addf(&commit_mark_sb, ":%d", mark);

		merge_revision_hash(&meta_revision_hash, ps->revision_hash);
		mark = fast_export_commit_meta(branch_name,
						0,
						&meta_revision_hash,
						ps->revision_hash,
						ps->cancellation_point,
						commit_mark_sb.buf,
						meta_mark_sb.len ? meta_mark_sb.buf : NULL);
		strbuf_reset(&meta_mark_sb);
		strbuf_addf(&meta_mark_sb, ":%d", mark);

		ps = ps->next;
	}
	if (psnum) {
		tracef("Branch: %s Commits number: %d", branch_name, psnum);

		if (initial_import && !strcmp(branch_name, "HEAD")) {
			helper_printf("reset HEAD\n");
			helper_printf("from %s\n", commit_mark_sb.buf);
		}

		helper_printf("checkpoint\n");
		helper_printf("sync\n");
		helper_flush();
		helper_strbuf_getline(&buf_sb);
		if (strcmp(buf_sb.buf, "sync"))
			die("fast-import sync failed: %s", buf_sb.buf);
		invalidate_ref_cache(NULL);
	}
	else {
		tracef("Branch: %s is up to date", branch_name);
	}

	strbuf_release(&commit_mark_sb);
	strbuf_release(&meta_mark_sb);
	strbuf_release(&branch_ref);
	strbuf_release(&branch_private_ref);
	strbuf_release(&meta_branch_ref);
	strbuf_release(&buf_sb);
	free_hash(&meta_revision_hash);
	return 0;
}

static int import_tag_by_name(const char *branch_name)
{
	int mark;
	struct hash_table tag_revision_hash = HASH_TABLE_INIT;

	tracef("importing CVS tag %s", branch_name);

	mark = do_initial_import(branch_name, 1, 0, &tag_revision_hash);
	free_revision_meta(&tag_revision_hash);

	return !mark;
}

static int cmd_batch_import(struct string_list *list)
{
	struct string_list_item *item;
	const char *branch_name;

	for_each_string_list_item(item, list) {
		if (!(branch_name = gettext_after(item->string, "import refs/heads/"))) {
			if ((branch_name = gettext_after(item->string, "import refs/tags/")))
				item->util = BRANCH_IS_TAG;
			else
				die("Malformed import command (wrong ref prefix) %s", item->string);
		}

		memmove(item->string, branch_name, strlen(branch_name) + 1); // move including \0
	}

	import_branch_list = list;
	import_start_time = time(NULL);

	if (show_progress)
		progress_state = start_progress("receiving revisions", 0);

	item = unsorted_string_list_lookup(list, "HEAD");
	if (item) {
		import_branch_by_name(item->string);
		item->util = BRANCH_IMPORTED;
	}

	for_each_string_list_item(item, list) {
		if (item->util == BRANCH_NOT_IMPORTED) {
			import_branch_by_name(item->string);
			item->util = BRANCH_IMPORTED;
		}
	}

	for_each_string_list_item(item, list) {
		if (item->util == BRANCH_IS_TAG) {
			import_tag_by_name(item->string);
		}
	}

	if (show_progress)
		stop_progress(&progress_state);
	helper_printf("done\n");
	helper_flush();
	return 0;
}

struct sha1_hash_pair {
	unsigned char *sha1;
	struct hash_table **revision_meta_hash;
};

static int find_commit_meta_on_ref(const char *branch_name, const unsigned char *sha1, int flags, void *data)
{
	struct strbuf meta_ref_sb = STRBUF_INIT;
	struct sha1_hash_pair *args = data;

	strbuf_addf(&meta_ref_sb, "%s%s", get_meta_ref_prefix(), branch_name);
	load_revision_meta(args->sha1, meta_ref_sb.buf, NULL, args->revision_meta_hash);

	strbuf_release(&meta_ref_sb);
	if (*args->revision_meta_hash)
		return 1;
	return 0;
}

static int find_commit_meta(unsigned char *sha1, struct hash_table **revision_meta_hash)
{
	struct sha1_hash_pair args = { sha1, revision_meta_hash };
	*revision_meta_hash = NULL;

	for_each_ref_in(get_meta_ref_prefix(), find_commit_meta_on_ref, &args);
	if (!*revision_meta_hash)
		return -1;
	return 0;
}

static int prepare_cvsfile(void *ptr, void *data)
{
	struct cvs_revision *rev = ptr;
	struct cvsfile **fileit = data;

	cvsfile_init(*fileit);
	strbuf_addstr(&(*fileit)->path, rev->path);
	strbuf_addstr(&(*fileit)->revision, rev->revision);
	(*fileit)++;
	return 0;
}

static int save_new_tag_meta(unsigned char *sha1, const char *tag_name, int istag, struct hash_table *revision_meta_hash)
{
	struct strbuf meta_ref_sb = STRBUF_INIT;

	strbuf_addf(&meta_ref_sb, "%s%s", istag ? get_meta_tags_ref_prefix() : get_meta_ref_prefix(), tag_name);
	save_revision_meta(sha1, meta_ref_sb.buf, "new tag pushed", revision_meta_hash);
	strbuf_release(&meta_ref_sb);
	return 0;
}

static int push_tag_to_cvs(const char *tag_name, int istag, struct hash_table *revision_meta_hash)
{
	struct cvsfile *files, *it;
	unsigned int count = revision_meta_hash->nr;
	int rc;
	int i;

	files = xcalloc(count, sizeof(*files));
	it = files;

	for_each_hash(revision_meta_hash, prepare_cvsfile, &it);

	rc = cvs_tag(cvs, tag_name, istag, files, count);

	for (i = 0; i < count; i++)
		cvsfile_release(&files[i]);
	free(files);

	return rc;
}

/*
 * iterates over commits until it finds the one with cvs metadata (point where
 * git local topic branch was started)
 */
static int prepare_push_commit_list(unsigned char *sha1, const char *meta_ref, struct commit_list **push_list)
{
	struct hash_table *revision_meta_hash;
	struct commit *commit;

	*push_list = NULL;

	commit = lookup_commit(sha1);
	for (;;) {
		if (parse_commit(commit))
			die("cannot parse commit %s", sha1_to_hex(commit->object.sha1));

		tracef("adding push list commit: %s date: %s commit: %p",
			sha1_to_hex(commit->object.sha1), show_date(commit->date, 0, DATE_NORMAL), commit);
		commit_list_insert(commit, push_list);
		if (meta_ref)
			load_revision_meta(commit->object.sha1, meta_ref, NULL, &revision_meta_hash);
		else
			find_commit_meta(commit->object.sha1, &revision_meta_hash);
		if (revision_meta_hash) {
			commit->util = revision_meta_hash;
			tracef("adding push list commit meta: %p", commit);
			break;
		}

		if (!commit->parents)
			break;
		if (commit_list_count(commit->parents) > 1)
			die("pushing of merge commits is not supported");

		commit = commit->parents->item;
	}

	if (!revision_meta_hash) {
		free_commit_list(*push_list);
		*push_list = NULL;
		return -1;
	}

	return 0;
}

/*
 * TODO: move this stuff somewhere. Pack in structure and add util to diff_options?
 */
static struct string_list new_directory_list = STRING_LIST_INIT_DUP; // used to create non-existing directories
static struct string_list touched_file_list = STRING_LIST_INIT_DUP; // used for status before pushing changes
static struct hash_table *base_revision_meta_hash = NULL;
static struct commit *current_commit = NULL; // used to save string_list of file path / cvsfile per commit
struct sha1_mod {
	unsigned char sha1[20];
	unsigned mode;
	int addremove;
};

static struct sha1_mod *make_sha1_mod(const unsigned char *sha1, unsigned mode, int addremove)
{
	struct sha1_mod *sm = xmalloc(sizeof(*sm));
	hashcpy(sm->sha1, sha1);
	sm->mode = mode;
	sm->addremove = addremove;

	return sm;
}

static void add_commit_file(struct commit *commit, const char *path, const unsigned char *sha1, unsigned mode, int addremove)
{
	struct string_list *file_list = current_commit->util;
	if (!file_list) {
		file_list = xcalloc(1, sizeof(*file_list));
		file_list->strdup_strings = 1;
		current_commit->util = file_list;
	}

	string_list_append(file_list, path)->util = make_sha1_mod(sha1, mode, addremove);;
}

static void on_file_change(struct diff_options *options,
			   unsigned old_mode, unsigned new_mode,
			   const unsigned char *old_sha1,
			   const unsigned char *new_sha1,
			   int old_sha1_valid, int new_sha1_valid,
			   const char *concatpath,
			   unsigned old_dirty_submodule, unsigned new_dirty_submodule)
{
	struct cvs_revision *rev;

	if (S_ISLNK(new_mode))
		die("CVS does not support symlinks: %s", concatpath);

	if ((S_ISDIR(old_mode) && !S_ISDIR(new_mode)) ||
	    (!S_ISDIR(old_mode) && S_ISDIR(new_mode)))
		die("CVS cannot handle file paths which used to de directories and vice versa: %s", concatpath);

	if (S_ISDIR(new_mode))
		return;

	if (!S_ISREG(new_mode))
		die("CVS cannot handle non-regular files: %s", concatpath);

	if (old_mode != new_mode && !ignore_mode_change)
		die("CVS does not support file permission changes. "
		    "Set cvshelper.ignoreModeChange to true if you want to ignore and push anyway.");

	if (old_mode != new_mode && !memcmp(old_sha1, new_sha1, 20)) {
		tracef("ignoring file because only permissions were"
				" changed (CVS does not support file permission changes): %s "
				"mode: %o -> %o "
				"sha: %d %s -> %d %s",
				concatpath,
				old_mode, new_mode,
				old_sha1_valid,
				sha1_to_hex(old_sha1),
				new_sha1_valid,
				sha1_to_hex(new_sha1));
		return;
	}

	tracef("file changed: %s "
			"mode: %o -> %o "
			"sha: %d %s -> %d %s",
			concatpath,
			old_mode, new_mode,
			old_sha1_valid,
			sha1_to_hex(old_sha1),
			new_sha1_valid,
			sha1_to_hex(new_sha1));

	/*
	 * TODO: verify that old meta exists
	 * - note case when file added in previous commit and no metadata exist
	 */
	rev = lookup_hash(hash_path(concatpath), base_revision_meta_hash);
	if (!rev) {
		/*
		 * FIXME:
		 */
	}
	string_list_append(&touched_file_list, concatpath);
	add_commit_file(current_commit, concatpath, new_sha1, new_mode, 0);
}

static void on_file_addremove(struct diff_options *options,
			      int addremove, unsigned mode,
			      const unsigned char *sha1,
			      int sha1_valid,
			      const char *concatpath, unsigned dirty_submodule)
{
	if (S_ISLNK(mode))
		die("CVS does not support symlinks: %s", concatpath);

	tracef("%s %s: %s "
			"mode: %o "
			"sha: %d %s",
			S_ISDIR(mode) ? "dir" : "file",
			addremove == '+' ? "add" : "remove",
			concatpath,
			mode,
			sha1_valid,
			sha1_to_hex(sha1));

	if (S_ISDIR(mode)) {
		if (addremove == '+')
			string_list_append(&new_directory_list, concatpath);
		return;
	}

	if (!S_ISREG(mode))
		die("CVS cannot handle non-regular files: %s", concatpath);

	/*
	 * FIXME: meta needed?
	 */
	string_list_append(&touched_file_list, concatpath);
	/*
	 * FIXME: add/remove flag
	 */
	add_commit_file(current_commit, concatpath, sha1, mode, addremove);
}

static int check_file_list_remote_status(const char *cvs_branch, struct string_list *file_list, struct hash_table *revision_meta_hash)
{
	struct cvsfile *files;
	struct cvs_revision *rev;
	int count = file_list->nr;
	int rc;
	int i;

	files = xcalloc(count, sizeof(*files));
	for (i = 0; i < count; i++) {
		cvsfile_init(&files[i]);
		strbuf_addstr(&files[i].path, file_list->items[i].string);

		rev = lookup_hash(hash_path(files[i].path.buf), base_revision_meta_hash);
		if (rev) {
			strbuf_addstr(&files[i].revision, rev->revision);
			files[i].isdead = rev->isdead;
		}
		else {
			files[i].isnew = 1;
		}

		tracef("status: %s rev: %s isdead: %u",
			files[i].path.buf, files[i].revision.buf, files[i].isdead);
	}

	rc = cvs_status(cvs, cvs_branch, files, count);
	for (i = 0; i < count; i++)
		cvsfile_release(&files[i]);
	free(files);
	return rc;
}

static int create_remote_directories(const char *cvs_branch, struct string_list *new_directory_list)
{
	struct string_list_item *item;
	for_each_string_list_item(item, new_directory_list) {
		tracef("directory add %s", item->string);
	}
	return cvs_create_directories(cvs, cvs_branch, new_directory_list);
}

static int prepare_file_content(struct cvsfile *file, void *data)
{
	enum object_type type;
	void *buf;
	unsigned long size;
	struct sha1_mod *sm;

	sm = file->util;
	if (!sm)
		die("Cannot prepare file content for commit, no sha1 known");

	if (sm->addremove == '-')
		return 0;

	buf = read_sha1_file(sm->sha1, &type, &size);
	if (!buf)
		return -1;

	/*
	 * FIXME: no reallocs
	 */
	strbuf_attach(&file->file, buf, size, size);
	return 0;
}

static void release_file_content(struct cvsfile *file, void *data)
{
	strbuf_release(&file->file);
}

static char *run_export_hook(const char *hook_message)
{
	struct strbuf sb = STRBUF_INIT;
	FILE *fp;
	int rc;

	fp = fopen(git_path(export_commit_edit), "w");
	if (fp == NULL)
		die_errno(_("could not open '%s'"), git_path(export_commit_edit));
	if (fwrite(hook_message, 1, strlen(hook_message), fp) < strlen(hook_message))
		die("could not write %s", export_commit_edit);
	fclose(fp);

	rc = run_hook(NULL, "cvs-export-commit", git_path(export_commit_edit), NULL);
	if (rc)
		die("cvs-export-commit hook rc %d, abording export", rc);

	fp = fopen(git_path(export_commit_edit), "r");
	if (fp == NULL)
		die_errno(_("could not open '%s'"), git_path(export_commit_edit));

	if (strbuf_read_file(&sb, git_path(export_commit_edit), 0) < 0)
		die_errno(_("could not read '%s'"), git_path(export_commit_edit));
	fclose(fp);
	return strbuf_detach(&sb, NULL);
}

static int push_commit_to_cvs(struct commit *commit, const char *cvs_branch, struct hash_table *revision_meta_hash)
{
	struct cvs_revision *rev;
	struct string_list *file_list;
	struct string_list_item *item;
	struct cvsfile *files;
	struct sha1_mod *sm;
	const char *commit_message;
	struct strbuf meta_ref_sb = STRBUF_INIT;
	struct strbuf meta_commit_msg_sb = STRBUF_INIT;
	char *hook_message = NULL;
	int count;
	int rc;
	int i;
	int need_new_cvs_session = 0;
	if (!commit->util)
		return -1;

	tracef("pushing commit %s to CVS branch %s", sha1_to_hex(commit->object.sha1), cvs_branch);
	strbuf_addstr(&meta_commit_msg_sb, "cvs meta update\n");

	file_list = commit->util;
	sort_string_list(file_list);
	count = file_list->nr;

	files = xcalloc(count, sizeof(*files));
	for (i = 0; i < count; i++) {
		cvsfile_init(&files[i]);
		item = &file_list->items[i];
		sm = item->util;
		if (!sm)
			die("No sha1 mod accociated with file being checked in");

		files[i].util = sm;
		files[i].isexec = !!(sm->mode & 0111);
		files[i].mode = sm->mode;
		tracef("check in %c file: %s sha1: %s mod: %.4o",
				sm->addremove ? sm->addremove : '*', item->string, sha1_to_hex(sm->sha1), sm->mode);
		strbuf_addstr(&files[i].path, item->string);
		if (sm->addremove == '+') {
			files[i].isnew = 1;
		}
		else if (sm->addremove == '-') {
			files[i].isdead = 1;
			need_new_cvs_session = 1;
		}

		rev = lookup_hash(hash_path(files[i].path.buf), revision_meta_hash);
		if (rev) {
			strbuf_addstr(&files[i].revision, rev->revision);
			/*
			 * warn if file is new (file new and isdead when it was
			 * removed and now is to be added again)
			 */
			if (files[i].isnew) {
				if (!rev->isdead)
					warning("file: %s meta rev: %s is supposed to be new, but revision metadata was found",
						files[i].path.buf, files[i].revision.buf);
				else
					strbuf_reset(&files[i].revision);
			}
		}
		else {
			if (files[i].isnew)
				add_cvs_revision_hash(revision_meta_hash, files[i].path.buf, "0", 0, 0, 1, NULL);
			else
				die("file: %s has not revision metadata, and not new", files[i].path.buf);
		}
	}

	find_commit_subject(commit->buffer, &commit_message);
	tracef("export hook '%s'", commit->buffer);
	if (have_export_hook) {
		hook_message = strstr(commit->buffer, "author ");
		if (!hook_message)
			die("unexpected commit format '%s'", commit->buffer);
		commit_message = hook_message = run_export_hook(hook_message);
	}

	/*
	 * FIXME: CVS cannot handle few commits during single session sometimes.
	 * Something has to do with same files added/modified/deleted. Try to
	 * minimize new cvs sessions.
	 */
	if (need_new_cvs_session) {
		tracef("extra cvs session");
		rc = cvs_terminate(cvs);
		if (rc)
			die("ungraceful cvs session termination");
		cvs = cvs_connect(cvsroot, cvsmodule);
		if (!cvs)
			die("failed to establish new cvs session");
	}
	rc = cvs_checkin(cvs, cvs_branch, commit_message, files, count, prepare_file_content, release_file_content, NULL);
	if (!rc) {
		for (i = 0; i < count; i++) {
			rev = lookup_hash(hash_path(files[i].path.buf), revision_meta_hash);
			if (!rev)
				die("commit succeeded, but cannot find meta file to update: %s", files[i].path.buf);
			if (!rev->revision)
				die("commit succeeded, but cannot find meta file revision to update: %s", files[i].path.buf);
			free(rev->revision);
			rev->revision = strbuf_detach(&files[i].revision, NULL);
			rev->isdead = files[i].isdead;
			//tracef("new rev: %s %s", rev->revision, rev->path);
			/*if (!files[i].isdead)
				rev->revision = strbuf_detach(&files[i].revision, NULL);
			else
				rev->revision = NULL;*/
			strbuf_addf(&meta_commit_msg_sb, "%s %s %s\n",
							 rev->isdead ? "deleted" : "updated",
							 rev->revision,
							 rev->path);
		}
		/*
		 * save metadata
		 */
		strbuf_addf(&meta_ref_sb, "%s%s", get_meta_ref_prefix(), cvs_branch);
		save_revision_meta(commit->object.sha1, meta_ref_sb.buf, meta_commit_msg_sb.buf, revision_meta_hash);
	}

	for (i = 0; i < count; i++)
		cvsfile_release(&files[i]);
	free(files);
	strbuf_release(&meta_ref_sb);
	strbuf_release(&meta_commit_msg_sb);
	if (hook_message)
		free(hook_message);
	return rc;
}

static int push_commit_list_to_cvs(struct commit_list *push_list, const char *cvs_branch)
{
	struct commit *commit;
	struct commit *parent;
	struct commit *base;
	struct commit_list *push_list_it;
	struct hash_table *revision_meta_hash;

	struct diff_options diffopt;
	diff_setup(&diffopt);
	diffopt.change = on_file_change;
	diffopt.add_remove = on_file_addremove;
	DIFF_OPT_SET(&diffopt, RECURSIVE);
	DIFF_OPT_SET(&diffopt, TREE_IN_RECURSIVE);
	DIFF_OPT_SET(&diffopt, IGNORE_SUBMODULES);

	base = push_list->item;
	revision_meta_hash = base->util;
	if (!revision_meta_hash)
		die("push failed: base commit does not have CVS metadata");

	tracef("base commit: %s date: %s on CVS branch: %s",
			sha1_to_hex(base->object.sha1), show_date(base->date, 0, DATE_NORMAL), cvs_branch);

	base_revision_meta_hash = revision_meta_hash;
	string_list_clear(&new_directory_list, 0);
	string_list_clear(&touched_file_list, 0);

	push_list_it = push_list;
	while ((push_list_it = push_list_it->next)) {
		commit = push_list_it->item;
		parent = commit->parents->item;

		tracef("-----------------------------");
		tracef("pushing: %s date: %s to CVS branch: %s",
			sha1_to_hex(commit->object.sha1), show_date(commit->date, 0, DATE_NORMAL), cvs_branch);

		current_commit = commit;
		diff_tree_sha1(parent->object.sha1, commit->object.sha1, "", &diffopt);
	}

	sort_string_list(&new_directory_list);
	string_list_remove_duplicates(&new_directory_list, 0);
	sort_string_list(&touched_file_list);
	string_list_remove_duplicates(&touched_file_list, 0);

	/*
	 * filtered later
	 *
	push_list_it = push_list;
	while ((push_list_it = push_list_it->next)) {
		commit = push_list_it->item;
		if (!commit->util)
			die("No files changed in pending commit: %s", sha1_to_hex(commit->object.sha1));
	}
	*/
	if (new_directory_list.nr &&
	    create_remote_directories(cvs_branch, &new_directory_list))
		return 1;

	if (check_file_list_remote_status(cvs_branch, &touched_file_list, revision_meta_hash)) {
		error("You are not up-to date. Update your local repository copy first.");
		return 1;
	}

	push_list_it = push_list;
	while ((push_list_it = push_list_it->next)) {
		commit = push_list_it->item;
		if (commit->util) {
			if (push_commit_to_cvs(commit, cvs_branch, revision_meta_hash))
				return 1;
		}
		else {
			warning("Skipping empty commit: %s", sha1_to_hex(commit->object.sha1));
		}
	}
	/*
	 * TODO:
	 * - update metadata???
	 * - commit list cleanup
	 * - util in commit list cleanup
	 */
	push_list_it = push_list;
	while ((push_list_it = push_list_it->next)) {
		commit = push_list_it->item;
		if (commit->util) {
			string_list_clear(commit->util, 1);
			free(commit->util);
			commit->util = 0;
		}
	}

	return 0;
}

static int push_branch(const char *src, const char *dst, int force)
{
	int rc = -1;
	int is_new_branch = 0;
	const char *cvs_branch;
	unsigned commits_count;
	unsigned char sha1[20];
	struct strbuf meta_ref_sb = STRBUF_INIT;
	struct commit_list *push_list = NULL;

	cvs_branch = strrchr(dst, '/');
	if (!cvs_branch)
		die("Malformed destination branch name");
	cvs_branch++;

	if (get_sha1(src, sha1))
		die(_("Failed to resolve '%s' as a valid ref."), src);

	strbuf_addf(&meta_ref_sb, "%s%s", get_meta_ref_prefix(), cvs_branch);
	if (!ref_exists(meta_ref_sb.buf))
		is_new_branch = 1;

	if (is_new_branch && single_commit_push)
		die("single commit push cannot be used with new branch creation");

	tracef("pushing %s to %s (CVS branch: %s) force: %d new branch: %d",
			src, dst, cvs_branch, force, is_new_branch);

	if (prepare_push_commit_list(sha1, is_new_branch ? NULL :  meta_ref_sb.buf, &push_list))
		die("prepare_push_commit_list failed");

	if (is_new_branch &&
	    push_list->item) {
		if (push_tag_to_cvs(cvs_branch, 0, push_list->item->util))
			die("Cannot create CVS branch %s", cvs_branch);
		else
			save_new_tag_meta(sha1, cvs_branch, 0, push_list->item->util);
	}

	/*
	 * prepare_push_commit_list always put commit with cvs metadata first,
	 * that should not be pushed
	 */
	commits_count = commit_list_count(push_list);
	if (single_commit_push) {
		unsigned char single_commit_sha1[20];
		struct commit *commit;

		if (commits_count != 2)
			die("single commit push failed: %u commits pending", commits_count - 1);

		if (get_sha1_commit(single_commit_push, single_commit_sha1))
			die("cannot resolve single commit name: '%s'", single_commit_push);

		commit = push_list->next->item;
		if (memcmp(single_commit_sha1, commit->object.sha1, 20))
			die("single commit push failed: commit sha mismatch '%s' vs '%s'",
			    sha1_to_hex(single_commit_sha1), sha1_to_hex(commit->object.sha1));

		tracef("pushing single commit '%s'", sha1_to_hex(single_commit_sha1));
	}

	if (commits_count > 1) {
		if (!push_commit_list_to_cvs(push_list, cvs_branch)) {
			if (no_refs_update_on_push)
				strbuf_addstr(&push_error_sb, "NO_REFS_UPDATE_ON_PUSH "
					      "was set. Perform fetch to get pushed changes from CVS.");
			else
				rc = 0;
		}
	}
	else {
		tracef("Nothing to push");
		rc = 0;
	}

	free_commit_list(push_list);
	strbuf_release(&meta_ref_sb);
	return rc;
}

static int push_tag(const char *src, const char *dst, int force)
{
	int rc = -1;
	const char *cvs_tag;
	struct strbuf meta_ref_sb = STRBUF_INIT;
	struct hash_table *revision_meta_hash;

	cvs_tag = strrchr(dst, '/');
	if (!cvs_tag)
		die("Malformed destination branch name");
	cvs_tag++;

	tracef("pushing %s to %s (CVS tag: %s) force: %d", src, dst, cvs_tag, force);

	unsigned char sha1[20];
	if (get_sha1(src, sha1))
		die(_("Failed to resolve '%s' as a valid ref."), src);

	strbuf_addf(&meta_ref_sb, "%s%s", get_meta_tags_ref_prefix(), cvs_tag);
	if (ref_exists(meta_ref_sb.buf) && !force)
		die("CVS tag %s already exist and no force was specified", cvs_tag);

	if (find_commit_meta(sha1, &revision_meta_hash)) {
		strbuf_reset(&push_error_sb);
		strbuf_addf(&push_error_sb, "%s tag has no CVS metadata. Only commits fetched "
			      "from or pushed to CVS can be tagged.", cvs_tag);
	}
	else if (!push_tag_to_cvs(cvs_tag, 1, revision_meta_hash)) {
		rc = save_new_tag_meta(sha1, cvs_tag, 1, revision_meta_hash);
	}

	if (revision_meta_hash) {
		free_revision_meta(revision_meta_hash);
		free(revision_meta_hash);
	}
	strbuf_release(&meta_ref_sb);
	return rc;
}

static int cmd_batch_push(struct string_list *list)
{
	struct string_list_item *item;
	const char *srcdst;
	const char *src;
	const char *dst;
	char *p;
	int force;
	int istag;
	int rc;

	single_commit_push = getenv("GIT_SINGLE_COMMIT_PUSH");
	if (single_commit_push && list->nr > 1)
		die("single commit push specified but multiple push refspecs passed");

	for_each_string_list_item(item, list) {
		if (!(srcdst = gettext_after(item->string, "push ")) ||
		    !strchr(srcdst, ':'))
			die("Malformed push command: %s", item->string);

		memmove(item->string, srcdst, strlen(srcdst) + 1); // move including \0
	}

	//import_branch_list = list;
	//import_start_time = time(NULL);

	//progress_state = start_progress("Receiving revisions", revisions_all_branches_total);

	for_each_string_list_item(item, list) {
		srcdst = item->string;
		force = 0;
		if (srcdst[0] == '+') {
			force = 1;
			srcdst++;
		}
		p = strchr(srcdst, ':');
		if (!p)
			die("Malformed push source-destination specification: %s", srcdst);
		*p++ = '\0';

		src = srcdst;
		dst = p;
		istag = !prefixcmp(src, "refs/tags/");

		strbuf_reset(&push_error_sb);
		if (istag)
			rc = push_tag(src, dst, force);
		else
			rc = push_branch(src, dst, force);

		if (!rc) {
			helper_printf("ok %s\n", dst);
		}
		else {
			if (!push_error_sb.len)
				strbuf_addstr(&push_error_sb, "pushing to CVS failed");
			helper_printf("error %s %s\n", dst, push_error_sb.buf);
		}
	}

	strbuf_release(&push_error_sb);
	helper_printf("\n");
	helper_flush();
	//stop_progress(&progress_state);
	return 0;
}

static void add_cvs_revision_cb(const char *branch_name,
				const char *path,
				const char *revision,
				const char *author,
				const char *msg,
				time_t timestamp,
				int isdead,
				void *data) {
	struct string_list *cvs_branch_list = data;
	struct string_list_item *li;
	struct cvs_branch *cvs_branch;

	if (is_cvs_import_excluded_path(path)) {
		tracef("%s ignored during import according to cvs-exclude", path);
		return;
	}

	li = unsorted_string_list_lookup(cvs_branch_list, branch_name);
	if (!li) {
		cvs_branch = new_cvs_branch(branch_name);
		string_list_append(cvs_branch_list, branch_name)->util = cvs_branch;
	}
	else {
		cvs_branch = li->util;
	}

	skipped += add_cvs_revision(cvs_branch, path, revision, author, msg, timestamp, isdead);
	revisions_all_branches_total++;
	if (show_progress) {
		display_progress(progress_state, revisions_all_branches_total);
		display_throughput(progress_state, cvs_read_total + cvs_written_total);
	}
}

static time_t update_since = 0;
static int on_each_ref(const char *branch_name, const unsigned char *sha1, int flags, void *data)
{
	struct string_list *cvs_branch_list = data;
	struct string_list_item *li;
	struct cvs_branch *cvs_branch;

	li = unsorted_string_list_lookup(cvs_branch_list, branch_name);
	if (!li) {
		cvs_branch = new_cvs_branch(branch_name);
		string_list_append(cvs_branch_list, branch_name)->util = cvs_branch;
	}
	else {
		cvs_branch = li->util;
	}

	if (!update_since ||
	    //FIXME: remember last update date somewhere or take last from
	    //branch: update_since < cvs_branch->last_revision_timestamp)
	    update_since < cvs_branch->last_revision_timestamp)
	    //update_since > cvs_branch->last_revision_timestamp)
		update_since = cvs_branch->last_revision_timestamp;
	return 0;
}

static int cmd_list(const char *line)
{
	int rc;
	cvs = cvs_connect(cvsroot, cvsmodule);
	if (!cvs)
		return -1;

	tracef("connected to cvs server");

	struct string_list_item *li;
	struct cvs_branch *cvs_branch;
	struct strbuf ref_sb = STRBUF_INIT;

	if (show_progress)
		progress_state = start_progress("fetching revisions info", 0);

	if (initial_import) {
		rc = cvs_rlog(cvs, 0, 0, &cvs_branch_list, &cvs_tag_list, add_cvs_revision_cb, &cvs_branch_list);
		if (rc == -1)
			die("rlog failed");
		tracef("Total revisions: %d", revisions_all_branches_total);
		tracef("Skipped revisions: %d", skipped);

		for_each_string_list_item(li, &cvs_branch_list) {
			cvs_branch = li->util;
			if (cvs_branch)
				finalize_revision_list(cvs_branch);
			helper_printf("? refs/heads/%s\n", li->string);
		}

		for_each_string_list_item(li, &cvs_tag_list) {
			helper_printf("? refs/tags/%s\n", li->string);
		}
		helper_printf("\n");
	}
	else {
		for_each_ref_in(get_meta_ref_prefix(), on_each_ref, &cvs_branch_list);
		/*
		 * handle case when last rlog didn't pick all files committed
		 * last second (hit during autotests)
		 */
		if (update_since > 0)
			update_since--;
		tracef("update since: %ld", update_since);

		/*
		 * FIXME: we'll skip branches which were not imported during
		 * initial import. If some changes for these branches arrives
		 * and import will pick it up this time, then history will be
		 * truncated. Have to detect this case and do full rlog for
		 * importing such branches.
		 */
		rc = cvs_rlog(cvs, update_since, 0, &cvs_branch_list, &cvs_tag_list, add_cvs_revision_cb, &cvs_branch_list);
		if (rc == -1)
			die("rlog failed");
		tracef("Total revisions: %d", revisions_all_branches_total);
		tracef("Skipped revisions: %d", skipped);

		for_each_string_list_item(li, &cvs_branch_list) {
			cvs_branch = li->util;
			if (cvs_branch)
				finalize_revision_list(cvs_branch);

			if (!cvs_branch || cvs_branch->rev_list->nr)
				helper_printf("? refs/heads/%s\n", li->string);
			else
				tracef("Branch: %s is up to date", li->string);
		}

		for_each_string_list_item(li, &cvs_tag_list) {
			strbuf_reset(&ref_sb);
			strbuf_addf(&ref_sb, "%s%s", get_meta_tags_ref_prefix(), li->string);
			if (update_tags || !ref_exists(ref_sb.buf))
				helper_printf("? refs/tags/%s\n", li->string);
		}

		helper_printf("\n");
	}
	if (show_progress)
		stop_progress(&progress_state);
	helper_flush();
	revisions_all_branches_total -= skipped;
	strbuf_release(&ref_sb);
	return 0;
}

static int print_meta_branch_name(const char *branch_name, const unsigned char *sha1, int flags, void *data)
{
	helper_printf("? refs/heads/%s\n", branch_name);
	return 0;
}

static int cmd_list_for_push(const char *line)
{
	cvs = cvs_connect(cvsroot, cvsmodule);
	if (!cvs)
		return -1;

	tracef("connected to cvs server");

	for_each_ref_in(get_meta_ref_prefix(), print_meta_branch_name, NULL);
	helper_printf("\n");

	helper_flush();
	return 0;
}

static int validate_tree_entry(const unsigned char *sha1, const char *base,
		int baselen, const char *filename, unsigned mode, int stage,
		void *meta)
{
	struct cvs_revision *file_meta;
	struct hash_table *revision_meta_hash = meta;
	char path[PATH_MAX];

	if (S_ISDIR(mode))
		return READ_TREE_RECURSIVE;

	snprintf(path, sizeof(path), "%s%s", base, filename);
	//tracef("validating: %s", path);
	file_meta = lookup_hash(hash_path(path), revision_meta_hash);
	if (!file_meta)
		die("no meta for file %s", path);
	if (file_meta->isdead)
		die("file %s is dead in meta", path);

	file_meta->util = 1; // mark revision is visited
	return 0;
}

static int zero_cvs_revision_util(void *rev, void *data)
{
	struct cvs_revision *file_meta = rev;
	file_meta->util = 0;

	return 0;
}

static int validate_cvs_revision_util(void *rev, void *data)
{
	struct cvs_revision *file_meta = rev;

	if (!file_meta->isdead &&
	    !file_meta->util)
		die("file %s exists in meta, but not in tree", file_meta->path);

	return 0;
}

static int validate_commit_meta_by_tree(const char *ref, struct hash_table *revision_meta_hash)
{
	struct pathspec pathspec;
	struct commit *commit;
	unsigned char sha1[20];
	int err;

	tracef("validating commit meta by tree");

	if (!ref_exists(ref))
		die("ref does not exist %s", ref);

	//if (get_sha1_commit(ref, sha1))
	if (get_sha1(ref, sha1))
		die("cannot find last commit on branch ref %s", ref);

	commit = lookup_commit(sha1);
	if (parse_commit(commit))
		die("cannot parse commit %s", sha1_to_hex(sha1));

	for_each_hash(revision_meta_hash, zero_cvs_revision_util, NULL);

	init_pathspec(&pathspec, NULL);
	err = read_tree_recursive(commit->tree, "", 0, 0, &pathspec,
				  validate_tree_entry, revision_meta_hash);
	free_pathspec(&pathspec);
	if (err == READ_TREE_RECURSIVE)
		err = 0;

	for_each_hash(revision_meta_hash, validate_cvs_revision_util, NULL);
	return err;
}

/*static int validate_cvs_branch_meta_by_tree(const char *branch_name)
{
	struct strbuf ref_sb = STRBUF_INIT;
	struct strbuf meta_ref_sb = STRBUF_INIT;
	struct hash_table *revision_meta_hash = NULL;
	unsigned char commit_sha1[20];
	int rc;

	strbuf_addf(&ref_sb, "%s%s", get_ref_prefix(), branch_name);
	strbuf_addf(&meta_ref_sb, "%s%s", get_meta_ref_prefix(), branch_name);

	if (get_sha1(ref_sb.buf, commit_sha1))
		die(_("Failed to resolve '%s' as a valid ref."), ref_sb.buf);

	if (!ref_exists(meta_ref_sb.buf))
		die("No metadata for branch %s", branch_name);

	load_revision_meta(commit_sha1, meta_ref_sb.buf, NULL, &revision_meta_hash);
	if (!revision_meta_hash)
		die("Cannot load metadata for branch %s", branch_name);

	rc = validate_commit_meta_by_tree(ref_sb.buf, revision_meta_hash);
	strbuf_release(&ref_sb);
	strbuf_release(&meta_ref_sb);
	return rc;
}*/

static void on_every_file_revision(const char *path, const char *revision, time_t timestamp, void *meta)
{
	struct cvs_revision *file_meta;
	struct hash_table *revision_meta_hash = meta;

	tracef("rls: validating: %s", path);
	if (is_cvs_import_excluded_path(path)) {
		tracef("%s ignored during meta validation according to cvs-exclude", path);
		return;
	}

	file_meta = lookup_hash(hash_path(path), revision_meta_hash);
	if (!file_meta)
		error("no meta for file %s", path);
	if (file_meta->isdead)
		error("file %s is dead in meta", path);
	if (strcmp(revision, file_meta->revision))
		error("file %s revision is wrong: meta %s cvs %s",
		    path, file_meta->revision, revision);

	file_meta->util = 1; // mark revision is visited
}

/*static int validate_cvs_branch_meta_by_cvs_rls(const char *branch_name)
{
	struct cvs_transport *cvs = cvs_connect(cvsroot, cvsmodule);
	if (!cvs)
		return -1;

	return cvs_rls(cvs, branch_name, 0, 0, on_every_file_revision, NULL);
}*/

static int validate_commit_meta_by_rls(const char *branch_name, time_t timestamp, struct hash_table *revision_meta_hash)
{
	int rc;
	struct cvs_transport *cvs = cvs_connect(cvsroot, cvsmodule);
	if (!cvs)
		return -1;

	for_each_hash(revision_meta_hash, zero_cvs_revision_util, NULL);

	tracef("validating commit meta by rls");

	rc = cvs_rls(cvs, branch_name, 0, timestamp, on_every_file_revision, revision_meta_hash);

	for_each_hash(revision_meta_hash, validate_cvs_revision_util, NULL);
	return rc;
}

static int validate_cvs_branch_meta(const char *branch_name)
{
	struct strbuf ref_sb = STRBUF_INIT;
	struct strbuf meta_ref_sb = STRBUF_INIT;
	struct hash_table *revision_meta_hash = NULL;
	time_t timestamp;
	unsigned char commit_sha1[20];
	int rc;

	strbuf_addf(&ref_sb, "%s%s", get_ref_prefix(), branch_name);
	strbuf_addf(&meta_ref_sb, "%s%s", get_meta_ref_prefix(), branch_name);

	if (get_sha1(ref_sb.buf, commit_sha1))
		die(_("Failed to resolve '%s' as a valid ref."), ref_sb.buf);

	if (!ref_exists(meta_ref_sb.buf))
		die("No metadata for branch %s", branch_name);

	load_revision_meta(commit_sha1, meta_ref_sb.buf, &timestamp, &revision_meta_hash);
	if (!revision_meta_hash)
		die("Cannot load metadata for branch %s", branch_name);

	rc = validate_commit_meta_by_tree(ref_sb.buf, revision_meta_hash);
	if (!rc) {
		if (!timestamp)
			tracef("skipping meta check by rls, no commit timestamp");
		else
			rc = validate_commit_meta_by_rls(branch_name, timestamp, revision_meta_hash);
	}
	strbuf_release(&ref_sb);
	strbuf_release(&meta_ref_sb);
	return rc;
}

static int do_command(struct strbuf *line)
{
	const struct input_command_entry *p = input_command_list;
	static struct string_list batchlines = STRING_LIST_INIT_DUP;
	static const struct input_command_entry *batch_cmd;
	/*
	 * commands can be grouped together in a batch.
	 * Batches are ended by \n. If no batch is active the program ends.
	 * During a batch all lines are buffered and passed to the handler function
	 * when the batch is terminated.
	 */
	if (line->len == 0) {
		if (batch_cmd) {
			batch_cmd->batch_fn(&batchlines);
			batch_cmd = NULL;
			string_list_clear(&batchlines, 0);
			return 0;	/* end of the batch, continue reading other commands. */
		}
		return 1;	/* end of command stream, quit */
	}
	if (batch_cmd) {
		if (prefixcmp(line->buf, batch_cmd->name))
			die("Active %s batch interrupted by %s", batch_cmd->name, line->buf);
		/* buffer batch lines */
		string_list_append(&batchlines, line->buf);
		return 0;
	}

	for (p = input_command_list; p->name; p++) {
		if (!prefixcmp(line->buf, p->name) && (strlen(p->name) == line->len ||
				line->buf[strlen(p->name)] == ' ')) {
			if (p->batchable) {
				batch_cmd = p;
				string_list_append(&batchlines, line->buf);
				return 0;
			}
			return p->fn(line->buf);
		}
	}
	die("Unknown command '%s'", line->buf);
	return 0;
}

static int parse_cvs_spec(const char *spec)
{
	/*
	 * TODO: make proper parsing
	 */
	char *idx;

	idx = strrchr(spec, ':');
	if (!idx)
		return -1;

	if (!memchr(spec, '/', idx - spec))
		return -1;

	cvsroot = xstrndup(spec, idx - spec);
	cvsmodule = xstrdup(idx + 1);

	tracef("CVSROOT: %s", cvsroot);
	tracef("CVSMODULE: %s", cvsmodule);

	return 0;
}

int git_cvshelper_config(const char *var, const char *value, void *dummy)
{
	char *str = NULL;

	if (!strcmp(var, "cvshelper.ignoremodechange")) {
		ignore_mode_change = git_config_bool(var, value);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.pushnorefsupdate")) {
		no_refs_update_on_push = git_config_bool(var, value);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.verifyimport")) {
		verify_import = git_config_bool(var, value);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.cvsprototrace")) {
		if (git_config_pathname((const char **)&str, var, value) || !str)
			return 1;

		setenv("GIT_TRACE_CVS_PROTO", str, 0);
		free(str);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.remotehelpertrace")) {
		if (git_config_pathname((const char **)&str, var, value) || !str)
			return 1;

		setenv("GIT_TRACE_CVS_HELPER", str, 0);
		free(str);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.trace")) {
		if (git_config_pathname((const char **)&str, var, value) || !str)
			return 1;

		setenv("GIT_TRACE_CVS", str, 0);
		free(str);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.filememorylimit")) {
		fileMemoryLimit = git_config_ulong(var, value);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.requireauthorconvert")) {
		require_author_convert = git_config_bool(var, value);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.dumbrlog")) {
		dumb_rlog = git_config_bool(var, value);
		return 0;
	}
	else if (!strcmp(var, "cvshelper.aggregatorfuzztime")) {
		fuzz_time = git_config_ulong(var, value);
		return 0;
	}

	return git_default_config(var, value, dummy);
}

static void cvs_branch_list_item_free(void *p, const char *str)
{
	if (p)
		free_cvs_branch(p);
}

int main(int argc, const char **argv)
{
	struct strbuf buf = STRBUF_INIT;
	static struct remote *remote;
	const char *cvs_root_module;

	if (getenv("WAIT_GDB"))
		sleep(5);

	set_proto_trace_tz(local_tzoffset(time(NULL)));
	setenv("TZ", "UTC", 1);
	tzset();

	git_extract_argv0_path(argv[0]);
	setup_git_directory();
	if (argc < 2 || argc > 3) {
		usage("git-remote-cvs <remote-name> [<url>]");
		return 1;
	}

	git_config(git_cvshelper_config, NULL);
	remote = remote_get(argv[1]);
	cvs_root_module = (argc == 3) ? argv[2] : remote->url[0];

	tracef("**************************************");

	if (parse_cvs_spec(cvs_root_module))
		die("Malformed repository specification. "
		    "Should be [:method:][[user][:password]@]hostname[:[port]]/path/to/repository:module/path");

	tracef("git_dir: %s", get_git_dir());

	if (!ref_exists("HEAD")) {
		tracef("Initial import!");
		initial_import = 1;
	}

	set_ref_prefix_remote(remote->name);
	tracef("ref_prefix %s", get_ref_prefix());
	tracef("private_ref_prefix %s", get_private_ref_prefix());

	if (find_hook("cvs-import-commit"))
		have_import_hook = 1;
	if (find_hook("cvs-export-commit"))
		have_export_hook = 1;

	if (getenv("NO_REFS_UPDATE_ON_PUSH"))
		no_refs_update_on_push = 1;

	if (getenv("VERIFY_ONLY")) {
		validate_cvs_branch_meta(getenv("VERIFY_ONLY"));
		return 0;
	}

	while (1) {
		helper_strbuf_getline(&buf);
		if (do_command(&buf))
			break;
		strbuf_reset(&buf);
	}

	string_list_clear_func(&cvs_branch_list, cvs_branch_list_item_free);
	string_list_clear(&cvs_tag_list, 0);
	if (cvs) {
		int ret = cvs_terminate(cvs);

		tracef("done, rc=%d", ret);
	}

	cvs_authors_store();
	free_cvs_import_exclude();
	free_cvs_lfsblob_filter();
	strbuf_release(&buf);
	return 0;
}
