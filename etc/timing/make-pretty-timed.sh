#!/bin/bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh"

trap "exit 1" SIGHUP SIGINT SIGTERM

source ./etc/timing/make-pretty-timed-defaults.sh "$@"

bash ./etc/timing/make-each-time-file.sh "$MAKE SEMICOLON=;" "$SINGLE_TIME_FILE" || exit 1
python ./etc/timing/make-one-time-file.py "$SINGLE_TIME_FILE" "$SINGLE_PRETTY_TIME_FILE" || exit 1
cat "$SINGLE_PRETTY_TIME_FILE"
echo
