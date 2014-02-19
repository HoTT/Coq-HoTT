#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR" 1>/dev/null

#"$DIR"/add_upstream.sh
# copy the push_remote script so it stays around after we change branches
cp "$DIR"/{push_remote,push_remote_tmp}.sh


if [ -z "$UPDATE_HTML" ]; then
    echo 'Not making html becuase $UPDATE_HTML variable not set.'
    exit 0
fi

EXTRA_ARGS="$("$DIR"/check_should_dry_run.sh "$@")"

echo 'Configuring git for pushing...'
git config --global user.name "Travis-CI Bot"
git config --global user.email "Travis-CI-Bot@travis.fake"

export MESSAGE="Autoupdate documentation with coqdoc and proviola

Generated with \`make html proviola\`"

echo '$ make html'
make html
make proviola -j4 -k
mv proviola-html proviola-html-bak
git remote update
echo '$ git checkout -b gh-pages upstream/gh-pages'
git checkout -b gh-pages upstream/gh-pages
rm -rf coqdoc-html
rm -rf proviola-html
mv html coqdoc-html
mv proviola-html-bak proviola-html
git add coqdoc-html/*
git add proviola-html/*

echo '$ git commit -am "'"$MESSAGE"'"'
git commit -m "$MESSAGE"
# use the copy of the script which stayed around when we changed branches
"$DIR"/push_remote_tmp.sh gh-pages:gh-pages $EXTRA_ARGS

# checkout the original commit
echo '$ git checkout HEAD@{2}'
git checkout HEAD@{2} -f

popd 1>/dev/null
