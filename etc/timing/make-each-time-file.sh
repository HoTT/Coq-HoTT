#!/usr/bin/env bash

if [ x"$1" = x ]
then
    # print help

    cat <<EOF

This is a helper script for make-pretty-timed.sh and
make-pretty-timed-diff.sh.


USAGE: make-each-time-file.sh MAKE-COMMAND NEW_FILENAME [OLD_FILENAME]

MAKE-COMMAND: The command which is used to make the library, such as
              `make` or `make -j2`

NEW_FILENAME: The name of the file to store the output of timing the
              compilation of the current state of the library

OLD_FILENAME: The name of the file to store the output of timing the
              compilation of the most recently committed state of the
              library.  If given, `git stash` is used to obtain the
              most recently committed state.  If this script is
              interrupted or finishes, `git stash pop` is used to
              restore the present state.  This means that all relevant
              files must be tracked by git to be handled properly.
EOF
fi

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh"

MAKE="$1"
NEW_FILE="$2"
OLD_FILE="$3"

if [ ! -z "$OLD_FILE" ]; then
    # make the old version

    # record the output of git stash, so we know whether or not
    # something has changed
    CHANGE="$(git stash)"
    # if we're interrupted, first run `git stash pop` to clean up
    trap "git stash pop && exit 1" SIGHUP SIGINT SIGTERM

    # we must `make clean` so we have a fresh slate, and time _all_
    # the files
    make clean
    # run the given `make` command, passing `TIMED=1` to get timing
    # and `-k` to continue even if files fail
    $MAKE TIMED=1 -k 2>&1 | tee "$OLD_FILE"


    # make the current version
    if [ ! -z "$(echo "$CHANGE" | grep "No local changes to save")" ]; then
        # there is no diff, so just copy the time file
	cp "$OLD_FILE" "$NEW_FILE"
    else
	# there is a diff, so restore the changes
	git stash pop
	# now if we're interrupted, we should only exit immediately,
	# not pop more stashes
	trap "exit 1" SIGHUP SIGINT SIGTERM
        # we must `make clean` so we have a fresh slate, and time
        # _all_ the files
	make clean
        # run the given `make` command, passing `TIMED=1` to get
        # timing and `-k` to continue even if files fail
	$MAKE TIMED=1 -k 2>&1 | tee "$NEW_FILE"
    fi
else
    # if we're only making one state of the library, we still must
    # `make clean` so we have a fresh slate, and time _all_ the files
    make clean
    # run the given `make` command, passing `TIMED=1` to get timing
    # and `-k` to continue even if files fail
    $MAKE TIMED=1 -k 2>&1 | tee "$NEW_FILE"
fi

popd 1>/dev/null
