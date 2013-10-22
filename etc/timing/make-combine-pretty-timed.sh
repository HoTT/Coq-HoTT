#!/bin/bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh"

trap "exit 1" SIGHUP SIGINT SIGTERM

source ./etc/timing/make-pretty-timed-defaults.sh "$@"

python ./etc/timing/make-both-time-files.py "$NEW_TIME_FILE" "$OLD_TIME_FILE" "$BOTH_TIME_FILE" || exit 1
cat "$BOTH_TIME_FILE"
echo
