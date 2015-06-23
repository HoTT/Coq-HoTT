#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR" 1>/dev/null

if [ -z "$UPDATE_AUTOGEN" ]; then
    echo 'Not making autogen becuase $UPDATE_AUTOGEN variable not set.'
    exit 0
fi

COMMITISH="$(git rev-parse HEAD)"

EXTRA_ARGS="$("$DIR"/check_should_dry_run.sh "$@")"

# copy the push_remote script so it stays around after we change branches
cp -f "$DIR"/{push_remote,push_remote_tmp}.sh

"$DIR"/configure_commit.sh

export MESSAGE="./autogen.sh"

echo '$ autoreconf -fvi'
autoreconf -fvi || exit $?
FILES=`cat etc/autoreconf-files`
BRANCH=`cat etc/autoreconf-branch`
echo '$ git checkout -b '"$BRANCH"
git checkout -b $BRANCH
git add -f $FILES
echo '$ git commit -am "'"$MESSAGE"'"'
git commit -m "$MESSAGE"
# use the copy of the script which stayed around when we changed branches
"$DIR"/push_remote_tmp.sh $BRANCH:$BRANCH -f $EXTRA_ARGS

# checkout the original commit
echo '$ git checkout '"$COMMITISH"
git checkout "$COMMITISH" -f

popd 1>/dev/null
