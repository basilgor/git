#ifndef AGGREGATOR_H
#define AGGREGATOR_H

#include <time.h>
#include "vcs-cvs/cvs-types.h"

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
	/*
	 * cvs_commit_hash used to find potential commit with same author + message
	 * which single file revision might belong to
	 */
	struct hash_table *cvs_commit_hash; // author_msg2ps -> cvs_commit hash

	/*
	 * revision_hash used to look up previos revision of a file
	 * to make sure, that previos revision commit goes before commit of current revision
	 */
	struct hash_table *revision_hash; // path -> cvs_revision hash
	struct cvs_revision_list *rev_list;
	struct cvs_commit_list *cvs_commit_list;

	/*
	 * last_commit_revision_hash contains latest revisions which are already
	 * in git repository, only newer revisions will be fetched from CVS.
	 * This hash is used to verify that no revisions are synchronized twice
	 * or skipped.
	 */
	struct hash_table *last_commit_revision_hash; // path -> cvs_revision hash
	time_t last_revision_timestamp;

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

void finalize_revision_list(struct cvs_branch *meta);
void aggregate_cvs_commits(struct cvs_branch *meta);
time_t find_first_commit_time(struct cvs_branch *meta);
int get_cvs_commit_count(struct cvs_branch *meta);
void free_cvs_branch(struct cvs_branch *meta);
void print_cvs_commit(struct cvs_commit *cm);
#endif
