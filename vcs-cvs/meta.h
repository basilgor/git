#ifndef META_H
#define META_H

#include "hash.h"
#include "string-list.h"

unsigned int hash_path(const char *path);

void set_ref_prefix_remote(const char *remote_name);
const char *get_meta_ref_prefix();
const char *get_ref_prefix();
const char *get_private_ref_prefix();

/*
 * struct represents a revision of a single file in CVS.
 * cvs_commit field is always initialized and used
 * as author and msg placeholder, it may be changed
 * later during patch aggregation
 */
struct cvs_revision {
	char *path;
	char *revision;
	unsigned int ismeta:1;
	unsigned int isdead:1;

	/*
	 * multiple revisions of a file was merged together during patch aggregation
	 */
	unsigned int ismerged:1;
	unsigned int isexec:1;

	/*
	 * file was pushed to cvs and fetching for verification is needed
	 */
	unsigned int ispushed:1;
	unsigned int mark:24;
	struct cvs_revision *prev;
	struct cvs_commit *cvs_commit;
	time_t timestamp;
};

struct cvs_revision_list {
	unsigned int size, nr;
	struct cvs_revision **item;
};

struct cvs_commit {
	time_t timestamp;
	time_t timestamp_last;
	char *author;
	char *msg;
	struct cvs_commit *next; // cvs_commit list <--- will be sorted by timestamp
	struct hash_table *revision_hash; // path -> cvs_revision hash
	time_t cancellation_point; // non zero if cvs_commit is save cancellation point
	unsigned int seq;
};

struct cvs_commit_list {
	struct cvs_commit *head;
	struct cvs_commit *tail;
};

/*
 * struct cvs_branch represents a branch in CVS
 * with all metadata needed for patch aggregation
 * and consistency validation
 */
struct cvs_branch {
	//TODO: branch name
	struct hash_table *cvs_commit_hash; // author_msg2ps -> cvs_commit hash
	struct hash_table *revision_hash; // path -> cvs_revision hash
	struct cvs_revision_list *rev_list;
	struct cvs_commit_list *cvs_commit_list;

	struct hash_table *last_commit_revision_hash; // path -> cvs_revision hash
	time_t last_revision_timestamp;

	unsigned int fuzz_time;
	void *util;
};

/*
 * main cmd parses options, parses refs, gives git branch ref and cvs branch
 */

struct cvs_branch *new_cvs_branch(const char *branch_name);
int add_cvs_revision(struct cvs_branch *meta,
		       const char *path,
		       const char *revision,
		       const char *author,
		       const char *msg,
		       time_t timestamp,
		       int isdead);

void add_cvs_revision_meta(struct cvs_branch *meta,
		       const char *path,
		       const char *revision,
		       int isdead,
		       int isexec,
		       int mark);

void add_cvs_revision_hash(struct hash_table *meta_hash,
		       const char *path,
		       const char *revision,
		       int isdead,
		       int isexec,
		       int mark);

void finalize_revision_list(struct cvs_branch *meta);
void aggregate_cvs_commits(struct cvs_branch *meta);
time_t find_first_commit_time(struct cvs_branch *meta);
int get_cvs_commit_count(struct cvs_branch *meta);
void free_cvs_branch(struct cvs_branch *meta);

/*
 * branch name to meta map
 */
struct meta_map_entry {
	char *branch_name;
	struct cvs_branch *meta;
};

struct meta_map {
	unsigned int size, nr;
	struct meta_map_entry *array;
};

#define for_each_cvs_branch(item,map) \
	for (item = (map)->array; item < (map)->array + (map)->nr; ++item)

void meta_map_init(struct meta_map *map);
void meta_map_add(struct meta_map *map, const char *branch_name, struct cvs_branch *meta);
struct cvs_branch *meta_map_find(struct meta_map *map, const char *branch_name);
void meta_map_release(struct meta_map *map);

/*
 * metadata work
 */
int load_cvs_revision_meta(struct cvs_branch *meta,
			   const char *commit_ref,
			   const char *notes_ref);

int save_cvs_revision_meta(struct cvs_branch *meta,
			   const char *commit_ref,
			   const char *notes_ref);

char *read_note_of(unsigned char sha1[20], const char *notes_ref, unsigned long *size);
//char *parse_meta_line(char *buf, unsigned long len, char **first, char **second, struct string_list *attr_lst, char *p);
char *parse_meta_line(char *buf, unsigned long len, char **first, char **second, char *p);

/*
revision=1.24.3.43,isdead=y,ispushed=y:path
 */
void format_meta_line(struct strbuf *line, struct cvs_revision *meta);

/*
 * return -1 on error
 * revision_meta_hash == NULL if metadata was not loaded
 */
int load_revision_meta(unsigned char *sha1, const char *notes_ref, struct hash_table **revision_meta_hash);
int save_revision_meta(unsigned char *sha1, const char *notes_ref, const char *msg, struct hash_table *revision_meta_hash);
int has_revision_meta(unsigned char *sha1, const char *notes_ref);

#endif
