#!/usr/bin/env bash

######################################################################
# Record the compilation performance of the current tip of the
# library and the previous commit, and compare them.
#
# USAGE: etc/timing/make-pretty-timed-diff-tip.sh -j<NUMBER OF THREADS TO USE>
#
# This script creates a file ($BOTH_TIME_FILE in
# etc/timing/make-pretty-timed-defaults.sh) with the duration of
# compilation of each file that is compiled by `make`, as well as the
# total duration, of both the current state of the library and the
# most recent commit.  Any arguments passed to this script are passed
# along to `make`.  Argument quoting is NOT preserved.  This script
# supports multiple threads (the `-j<n>` arguments to `make`).
#
# IMPORTANT NOTE: The performance will be successfully computed even
# if some files in the library fail to compile, so do not use the
# success of this script as an indicator that the library compiles.
#
# This script uses `git checkout` to change states; this script will
# exit if you have staged but uncomitted changes.  The preferred way
# to run this script is:
#
# $ ./etc/timing/make-pretty-timed-diff-tip.sh
# $ git commit --amend -em "$(git log -1 --pretty=%B; echo; cat ./time-of-build-both.log)"
#
# This will bring up an editor, where you should edit your commit
# message above the time profile, leaving at least one blank line
# before the table.  You may pass, e.g., -j2 to this script to have it
# use more threads.  You should not exceed the number of cores on your
# machine, or else the timing will not be accurate.
######################################################################

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh"

# exit immediately if killed
trap "exit 1" SIGHUP SIGINT SIGTERM

# get the names of the files we use
source ./etc/timing/make-pretty-timed-defaults.sh "$@"

# run make clean and make, on both the old state and the new state
bash ./etc/timing/make-each-time-file-tip.sh "$MAKE" "$NEW_TIME_FILE" "$OLD_TIME_FILE" || exit 1
# aggregate the results
bash ./etc/timing/make-combine-pretty-timed.sh "$@"
