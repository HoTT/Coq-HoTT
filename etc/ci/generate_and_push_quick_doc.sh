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


if [ -z "$UPDATE_QUICK_DOC" ]; then
    echo 'Not making quick doc becuase $UPDATE_QUICK_DOC variable not set.'
    exit 0
fi

EXTRA_ARGS="$("$DIR"/check_should_dry_run.sh "$@")"

echo 'Configuring git for pushing...'
git config --global user.name "Travis-CI Bot"
git config --global user.email "Travis-CI-Bot@travis.fake"

export MESSAGE="Autoupdate documentation with DepsToDot.hs"
echo '$ make HoTT.deps HoTTCore.deps'
make HoTT.deps HoTTCore.deps
# There must be a better way to insert titles than sed...
runhaskell etc/DepsToDot.hs --coqdocbase="http://hott.github.io/HoTT/proviola-html/" < HoTT.deps | sed s'/^digraph {/digraph "HoTT Library Dependency Graph" {/g' > HoTT.dot
runhaskell etc/DepsToDot.hs --coqdocbase="http://hott.github.io/HoTT/proviola-html/" < HoTTCore.deps | sed s'/^digraph {/digraph "HoTT Core Library Dependency Graph" {/g' > HoTTCore.dot
dot -Tsvg HoTT.dot -o HoTT.svg
dot -Tsvg HoTTCore.dot -o HoTTCore.svg
echo '$ git checkout -b gh-pages upstream/gh-pages'
git checkout -b gh-pages upstream/gh-pages
rm -rf dependencies
mkdir -p dependencies
mv HoTT.svg HoTTCore.svg dependencies/
git add dependencies/*.svg

echo '$ git commit -am "'"$MESSAGE"'"'
git commit -m "$MESSAGE"
# use the copy of the script which stayed around when we changed branches
"$DIR"/push_remote_tmp.sh gh-pages:gh-pages $EXTRA_ARGS

# checkout the original commit
echo '$ git checkout HEAD@{2}'
git checkout HEAD@{2} -f

popd 1>/dev/null
