#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

# only make if we should ($UPDATE_HTML is not empty) and we're the same as origin/master
"$DIR"/generate_and_push_doc.sh "$@" || exit $?
"$DIR"/generate_and_push_quick_doc.sh "$@" || exit $?
"$DIR"/update_tocs.sh "$@" || exit $?
"$DIR"/generate_and_push_dep_graphs.sh "$@" || exit $?
"$DIR"/autogen_and_push.sh "$@" || exit $?

popd 1>/dev/null
