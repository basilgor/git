#!/bin/bash

[ $# -ne 3 ] && echo "usage: $0 <newrepo> <cvsurl> <oldrepo>" && exit 1

PATH="/extdrive/src/git:$PATH:$(dirname $0)"
newrepo=$1
cvsurl=$2
oldrepo=$3

git init $newrepo
repogitdir=$(cd $newrepo/.git; pwd)
echo "repogitdir $repogitdir"
repocachedir="$(cd $newrepo/..; pwd)/bdbcache"
workdir=$(pwd)

#migrate-cache.sh $oldrepo $newrepo

cd $newrepo
git remote add cvs cvs:::fork:/home/dummy/tmp/moo/cvs_repo:mod/src
mkdir $repocachedir

export GIT_TRACE_CVS=$repogitdir/trace.log
export GIT_TRACE_CVS_HELPER=$repogitdir/cvshelper.log
export GIT_TRACE_CVS_PROTO=$repogitdir/cvsproto.log
#export GIT_CACHE_CVS_DIR=$repocachedir
#export GIT_CACHE_CVS_RLOG=$repocachedir/rlog
export GIT_CVS_IMPORT_LFS_FILTER=$workdir/lfsblob-filter

git fetch cvs 2>&1 | tee $repogitdir/git-fetch.log
