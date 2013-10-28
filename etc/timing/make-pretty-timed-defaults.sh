#!/bin/sh

# This is a helper script for make-pretty-timed.sh and
# make-pretty-timed-diff.sh.

# This file sets the default file names of the make-pretty-timed*.sh
# scripts, as well as setting up the MAKE variable.

export NEW_TIME_FILE=time-of-build-after.log
export OLD_TIME_FILE=time-of-build-before.log
export BOTH_TIME_FILE=time-of-build-both.log
export NEW_PRETTY_TIME_FILE=time-of-build-after-pretty.log
export SINGLE_TIME_FILE=time-of-build.log
export SINGLE_PRETTY_TIME_FILE=time-of-build-pretty.log
export TIME_SHELF_NAME=time-of-build-shelf

# this is fragile, I think; try to find a way to make this more
# robust.
export MAKE="make $@"
