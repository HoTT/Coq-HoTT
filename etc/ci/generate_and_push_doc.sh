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

COMMITISH="$(git rev-parse HEAD)"

EXTRA_ARGS="$("$DIR"/check_should_dry_run.sh "$@")"

"$DIR"/configure_commit.sh

export MESSAGE="Autoupdate documentation with coqdoc and proviola and time2html

Generated with \`make html proviola\`"

echo '$ make html'
make html || exit $?
make proviola -j4 TIMED=1 -k; make proviola TIMED=1 || exit $?
make timing-html || exit $?
mv proviola-html proviola-html-bak
mv timing-html timing-html-bak
git remote update
echo '$ git checkout -b gh-pages upstream/gh-pages'
git checkout -b gh-pages upstream/gh-pages
rm -rf coqdoc-html
rm -rf proviola-html
rm -rf timing-html
mv html coqdoc-html
mv proviola-html-bak proviola-html
mv timing-html-bak timing-html
git add coqdoc-html/*
git add proviola-html/*
git add timing-html/*

echo '$ git commit -am "'"$MESSAGE"'"'
git commit -m "$MESSAGE"
# use the copy of the script which stayed around when we changed branches
"$DIR"/push_remote_tmp.sh gh-pages:gh-pages $EXTRA_ARGS

# checkout the original commit
echo '$ git checkout '"$COMMITISH"
git checkout "$COMMITISH" -f

popd 1>/dev/null
