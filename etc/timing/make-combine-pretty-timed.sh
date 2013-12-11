#!/usr/bin/env bash

# This is a helper script for make-pretty-timed-diff.sh.

# This script is used to combine the outputs of make-each-time-file.sh
# into a single prettified table of compilation performance.

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh"

# Exit immediately if killed
trap "exit 1" SIGHUP SIGINT SIGTERM

# get the names of the files we use
source ./etc/timing/make-pretty-timed-defaults.sh "$@"

# aggregate the results
python ./etc/timing/make-both-time-files.py "$NEW_TIME_FILE" "$OLD_TIME_FILE" "$BOTH_TIME_FILE" || exit 1
# print out the results
cat "$BOTH_TIME_FILE"
# echo a final new line, because `cat` doesn't
echo
