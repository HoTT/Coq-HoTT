#!/bin/bash

######################################################################
# Record the compilation performance of the current state of the
# library
#
# USAGE: etc/timing/make-pretty-timed.sh -j<NUMBER OF THREADS TO USE>
#
# This script creates a file ($SINGLE_PRETTY_TIME_FILE in
# etc/timing/make-pretty-timed-defaults.sh) with the duration of
# compilation of each file that is compiled by `make`, as well as the
# total duration.  Any arguments passed to this script are passed
# along to `make`.  Argument quoting is NOT preserved. This script
# supports multiple threads (the `-j<n>` arguments to `make`).
#
# IMPORTANT NOTE: The performance will be successfully computed even
# if some files in the library fail to compile, so do not use the
# success of this script as an indicator that the library compiles.
#
# This script is most useful after you have already committed your
# changes, or when you do not care about comparing the current state
# with a previous state.
######################################################################

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh"

# exit immediately if killed
trap "exit 1" SIGHUP SIGINT SIGTERM

# get the names of the files we use
source ./etc/timing/make-pretty-timed-defaults.sh "$@"

# run make clean and make
bash ./etc/timing/make-each-time-file.sh "$MAKE SEMICOLON=;" "$SINGLE_TIME_FILE" || exit 1
# aggregate the results
python ./etc/timing/make-one-time-file.py "$SINGLE_TIME_FILE" "$SINGLE_PRETTY_TIME_FILE" || exit 1
# print out the results
cat "$SINGLE_PRETTY_TIME_FILE"
# echo a final new line, because `cat` doesn't
echo
