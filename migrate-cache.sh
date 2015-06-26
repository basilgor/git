#!/bin/bash

[ $# -ne 2 ] && echo "usage: $0 <oldrepo> <newrepo>" && exit 1

reposrc="$1/.git"
repodst="$2/.git"
revcachref="refs/cvsmeta/cache/revisions"

echo "migrating cache from $reposrc to $repodst"

hash=$(GIT_DIR=$reposrc git cat-file -p $revcachref | GIT_DIR=$repodst git hash-object -w --no-filters --stdin)
GIT_DIR=$repodst git update-ref "$revcachref" "$hash"
echo "$revcachref hash $hash"

files=$(GIT_DIR=$reposrc git cat-file -p $revcachref | wc -l)
i=0
GIT_DIR=$reposrc git cat-file -p $revcachref | while read line; do
    i=$((i+1))
    progress=$(bc <<< "scale=2; $i*100/$files")
    sha1=${line:0:40}
    echo -n "migrating $i/$files ($progress %) sha $sha1 -> "
    GIT_DIR=$reposrc git cat-file -p $sha1 | GIT_DIR=$repodst git hash-object -w --no-filters --stdin
done
