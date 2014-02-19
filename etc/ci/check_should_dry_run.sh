#!/usr/bin/env bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR" 1>/dev/null

BAD_REMOTES="$(git remote -v | grep origin | grep -v 'github.com/HoTT/HoTT')"

"$DIR"/add_upstream.sh 1>&2

git remote update 1>&2

UPSTREAM_DIFF="$(git log HEAD..upstream/master)"

EXTRA_ARGS=""

# only push for real if we line up
# only push if match upstream/master
if [ "$1" != "-f" ]; then
    if [ ! -z "$BAD_REMOTES" ]; then
	echo 'Not pushing doc because there are remotes which are not HoTT/HoTT:' 1>&2
	echo "$BAD_REMOTES" 1>&2
	EXTRA_ARGS="--dry-run"
    fi

    # only make the errata if we're the same as upstream/master
    if [ ! -z "$UPSTREAM_DIFF" ]; then
	echo "Not pushing doc beause we do not match with upstream/master; call '$0 -f' to force" 1>&2
	EXTRA_ARGS="--dry-run"
    fi
fi

echo "$EXTRA_ARGS"

popd 1>/dev/null
