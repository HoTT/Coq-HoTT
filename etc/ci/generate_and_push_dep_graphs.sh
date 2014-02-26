#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

#"$DIR"/add_upstream.sh
# copy the push_remote script so it stays around after we change branches
cp "$DIR"/{push_remote,push_remote_tmp}.sh


if [ -z "$UPDATE_DEP_GRAPHS" ]; then
    echo 'Not making quick doc becuase $UPDATE_DEP_GRAPHS variable not set.'
    exit 0
fi

EXTRA_ARGS="$("$DIR"/check_should_dry_run.sh "$@")"

echo 'Configuring git for pushing...'
git config --global user.name "Travis-CI Bot"
git config --global user.email "Travis-CI-Bot@travis.fake"

export MESSAGE="Autoupdate documentation with dpdgraphs"

echo '$ make svg-file-dep-graphs svg-aggregate-dep-graphs'
make svg-file-dep-graphs
make svg-aggregate-dep-graphs

mv file-dep-graphs file-dep-graphs-bak
git remote update
echo '$ git checkout -b gh-pages upstream/gh-pages'
git checkout -b gh-pages upstream/gh-pages
git rm -rf file-dep-graphs
mv file-dep-graphs-bak file-dep-graphs
git add file-dep-graphs/*.svg # file-dep-graphs/*.dot

echo '$ git commit -am "'"$MESSAGE"'"'
git commit -m "$MESSAGE"
# use the copy of the script which stayed around when we changed branches
"$DIR"/push_remote_tmp.sh gh-pages:gh-pages $EXTRA_ARGS

# checkout the original commit
echo '$ git checkout HEAD@{2}'
git checkout HEAD@{2} -f

popd 1>/dev/null
