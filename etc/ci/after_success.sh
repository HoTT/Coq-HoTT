#!/usr/bin/env bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

# only make if we should ($UPDATE_HTML is not empty) and we're the same as origin/master
if [ -z "$UPDATE_HTML" ]; then
    echo 'Not making html because $UPDATE_HTML is not set'
else
    "$DIR"/generate_and_push_doc.sh "$@"
fi

if [ -z "$UPDATE_QUICK_DOC" ]; then
    echo 'Not making quick doc because $QUICK_DOC is not set'
else
    "$DIR"/generate_and_push_quick_doc.sh "$@"
    "$DIR"/autogen_and_push.sh "$@"
fi

popd 1>/dev/null
