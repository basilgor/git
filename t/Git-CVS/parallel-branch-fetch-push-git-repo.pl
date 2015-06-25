#!/usr/bin/perl

use 5.008;
use strict;
use warnings;
use Cwd qw(abs_path);
use File::Path qw(make_path remove_tree);

die("usage $0 <gitrepo> [<testdir>] [<cvsroot>]") if scalar @ARGV < 1;

my $git_repo_origin = shift @ARGV;
my $testdir = shift @ARGV;
my $cvsroot = shift @ARGV;
my $cvs_repo;
my $cvs_client_repo;
my $git_repo;
my $git_repo2;

$testdir = "git-remote-cvs-testing" unless $testdir;
$git_repo_origin = abs_path($git_repo_origin) if -d $git_repo_origin;
$testdir = abs_path($testdir);

print "=> repo $git_repo_origin\n";
print "=> testdir $testdir\n";

$cvs_repo = "$testdir/cvs_repo";
$cvs_client_repo = "$testdir/cvs_client_repo";
$git_repo = "$testdir/git_repo";
$git_repo2 = "$testdir/git_repo2";

make_path($testdir, $cvs_repo, $cvs_client_repo)
	or die "failed to create directories $!";

chdir($testdir) or die "$!";

sub mk_cvs_repo() {
	$cvsroot = $cvs_repo unless $cvsroot;
	print "=> creating cvs repo $cvsroot\n";
	`cvs -d $cvsroot init`;
	die "cvs init $?" if $?;
	return $cvsroot;
}

sub mk_cvs_module_commit($;) {
	my $cvsroot = shift;
	print "=> making cvs repo initial commit\n";
	chdir($cvs_client_repo) or die "$!";
	`cvs -d $cvsroot co .`;
	die "cvs co $?" if $?;

	make_path("mod/src")
		or die "failed to create directories $!";

	`cvs -d $cvsroot add mod mod/src`;
	die "cvs add $?" if $?;

	`echo "dummy file" > mod/src/remove_me`;

	`cvs -d $cvsroot add mod/src/remove_me`;
	die "cvs add $?" if $?;

	`cvs -d $cvsroot commit -m "initial cvs commit" mod/src/remove_me`;
	die "cvs commit $?" if $?;

	chdir($testdir) or die "$!";
	return "mod/src";
}

$cvsroot = mk_cvs_repo() or die "mkcvsrepo";
my $cvsmodule = mk_cvs_module_commit($cvsroot);

chdir($testdir) or die "$!";
$ENV{GIT_TRACE_CVS_HELPER} = "$testdir/cvshelper.log";
$ENV{GIT_TRACE_CVS_PROTO} = "$testdir/cvsproto.log";
$ENV{GIT_TRACE_CVS} = "$testdir/cvstrace.log";

$cvsroot = ":fork:$cvsroot" unless $cvsroot =~ /^:/;

print "=> cloning cvs repo $cvsroot\n";
`git clone -o cvs cvs::$cvsroot:$cvsmodule $git_repo 2>&1 | tee "$testdir/cvsclone.log"`;
die "git clone cvs $?" if $?;

print "=> cloning cvs repo $cvsroot\n";
`git clone -o cvs cvs::$cvsroot:$cvsmodule $git_repo2 2>&1 | tee "$testdir/cvsclone.log"`;
die "git clone cvs $?" if $?;

print "=> cloning git repo\n";
chdir($git_repo) or die "$!";
`git remote add git $git_repo_origin`;
die "git remote add $?" if $?;

`git fetch git`;
die "git fetch $git_repo_origin $?" if $?;

print "=> cloning git repo2\n";
chdir($git_repo2) or die "$!";
`git remote add git $git_repo_origin`;
die "git remote add $?" if $?;

`git fetch git`;
die "git fetch $git_repo_origin $?" if $?;

#
# TODO: add multiple commits pushes
#

my $initial_cherry_pick = 1;
my $git_zero_sha1 = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";
my $commit = "";
#my $restart = $commit;
my $old_tree = "";
my $commits = 0;
my $head_sha;
my $fetched_count;
my $commits_per_iter = 1;
print "restarting from $commit\n";

my $pusher_repo = $git_repo;
my $fetcher_repo = $git_repo2;

open(my $gi, "-|", "git log --reverse --format=\"%H %T\" git/master") or
	die "Cannot run git log: $!\n";

while ((my $line = <$gi>)) {
	my ($commit_sha, $tree_sha) = split(' ', $line);
	print "\n-----------------------------------------------------------\n";
	print "=> commit $commit_sha tree $tree_sha\n";
	print "-----------------------------------------------------------\n";
	next if ($tree_sha eq $git_zero_sha1);
	next if $old_tree eq $tree_sha;
	#$restart = $commit_sha;
	$old_tree = $tree_sha;
	$commits++;

	print "=> pusher $pusher_repo\n";
	chdir($pusher_repo) or die "$!";

	`git cherry-pick --allow-empty $commit_sha`;
	die "git cherry-pick failed $?" if $?;
	next if $commits % $commits_per_iter;

	if ($initial_cherry_pick) {
		`git rm remove_me`;
		die "git rm failed" if $?;
		`git commit -m "initial file remove"`;
		die "git commit failed" if $?;
	}

	`git push cvs HEAD:HEAD 2>&1 | tee --append $testdir/cvspushfetch.log`;
	print "=> commits pushed: $commits\n";
	#sleep(2);

	print "=> fetcher $fetcher_repo\n";
	chdir($fetcher_repo) or die "$!";

	$head_sha = `git rev-parse cvs/HEAD`;
	die "git rev-parse failed" if $?;
	chomp($head_sha);

	`git fetch cvs 2>&1 | tee --append $testdir/cvspushfetch.log`;
	die "git fetch failed" if $?;

	my $test_tree_sha = `git log -1 --format="%T" cvs/HEAD`;
	die "git log failed" if $?;
	chomp($test_tree_sha);

	$fetched_count = `git log --oneline $head_sha..cvs/HEAD | wc -l`;
	print "=> fetched commits: $fetched_count\n";

	die "tree sha $test_tree_sha, should be $tree_sha" if ($test_tree_sha ne $tree_sha);
	#die "commits were splitted" if $fetched_count != 1 and !$initial_cherry_pick;
	print "commits were splitted $commits_per_iter vs $fetched_count" if $fetched_count != $commits_per_iter and !$initial_cherry_pick;

	#`git rebase cvs/HEAD`;
	#die("git rebase failed") if $?;
	`git reset --hard cvs/HEAD`;
	die("git reset --hard cvs/HEAD failed") if $?;

	print "=> commits pushed/fetched/verified: $commits\n";

	$initial_cherry_pick = 0;

	($pusher_repo, $fetcher_repo) = ($fetcher_repo, $pusher_repo);
}
close($gi);

#END {
#	print "restart from $restart\n";
#}
