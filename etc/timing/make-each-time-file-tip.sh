#!/usr/bin/env bash

if [ -z "$1" -o -z "$2" -o -z "$3" ]
then
    # print help

    cat <<EOF

This is a helper script for make-pretty-timed-diff-tip.sh.


USAGE: make-each-time-file-tip.sh MAKE-COMMAND NEW_FILENAME OLD_FILENAME

MAKE-COMMAND: The command which is used to make the library, such as
              `make` or `make -j2`

NEW_FILENAME: The name of the file to store the output of timing the
              compilation of the current state of the library

OLD_FILENAME: The name of the file to store the output of timing the
              compilation of the state of HEAD^. The command `git
              checkout` is used to obtain that state.  If this script
              is interrupted or finishes, `git checkout` is used to
              restore the current HEAD.  If there are staged but
              uncommitted changes, this script will exit immediately.

EOF
fi

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh"

MAKE="$1"
NEW_FILE="$2"
OLD_FILE="$3"

# ensure that we have no changes
if [ ! -z "$(git status | grep '^# Changes to be committed:$')" ]
then
    git status
    echo 'ERROR: You have staged but uncomitted changes.'
    echo '       Either `git stash` them, or `git commit` them, or remove them.'
    exit 1
fi

BRANCH=$(git symbolic-ref -q HEAD || git rev-parse -q --verify HEAD)
BRANCH_DISP="$(git branch | grep '^*' | sed s'/* //')"
if [ "$BRANCH_DISP" = "(no branch)" ]
then
    BRANCH_DISP="$(git reflog | head -n 1 | grep -o 'moving from .* to .*' | sed s'/moving from .* to \(.*\)/\1/g')"
    BRANCH_MOV="$BRANCH"
else
    BRANCH_MOV="$BRANCH_DISP"
fi
echo "Tip is $BRANCH_DISP ($BRANCH)"
echo 'If this is wrong, break immediately with ^C'


# make the old version

# if we're interrupted, first run `git checkout $HEAD` to clean up
trap "git checkout '$BRANCH_MOV' && exit 1" SIGHUP SIGINT SIGTERM

git checkout HEAD^

# we must `make clean` so we have a fresh slate, and time _all_ the
# files
make clean
# run the given `make` command, passing `TIMED=1` to get timing and
# `-k` to continue even if files fail
$MAKE TIMED=1 -k 2>&1 | tee "$OLD_FILE"


# there is a diff, so restore the changes
git checkout "$BRANCH_MOV"
# now if we're interrupted, we should only exit immediately
trap "exit 1" SIGHUP SIGINT SIGTERM
# we must `make clean` so we have a fresh slate, and time _all_ the
# files
make clean
# run the given `make` command, passing `TIMED=1` to get timing and
# `-k` to continue even if files fail
$MAKE TIMED=1 -k 2>&1 | tee "$NEW_FILE"

popd 1>/dev/null
