#!/bin/bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

"$DIR"/add_upstream.sh
# copy the push_remote script so it stays around after we change branches
cp "$DIR"/{push_remote,push_remote_tmp}.sh



#for testing, always build

if [ 0 != 0 ]; then
if [ -z "$UPDATE_HTML" ]; then
    echo 'Not making html becuase $UPDATE_HTML variable not set.'
    exit 0
fi

# only make the html with -f, or if we're the same as origin/master
if [ "$1" != "-f" ]; then
    if [ ! -z "$(git diff origin/master)" ]; then
	echo "Not making html beause we do not match with origin/master; call '$0 -f' to force"
	exit 0
    fi
fi
fi

echo 'Configuring git for pushing...'
git config --global user.name "Travis-CI Bot"
git config --global user.email "Travis-CI-Bot@travis.fake"

export MESSAGE="Autoupdate documentation with coqdoc and proviola

Generated with \`make html proviola\`"

echo '$ make html'
make html
make proviola -j16
mv proviola-html proviola-html-bak
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





# for testing, only push if we should
if [ -z "$UPDATE_HTML" ]; then
    echo 'Not making html becuase $UPDATE_HTML variable not set.'
    exit 0
fi

# only make the html with -f, or if we're the same as origin/master
if [ "$1" != "-f" ]; then
    if [ ! -z "$(git diff origin/master)" ]; then
	echo "Not making html beause we do not match with origin/master; call '$0 -f' to force"
	exit 0
    fi
fi



source "$DIR"/push_remote_tmp.sh gh-pages:gh-pages

# checkout the original commit
echo '$ git checkout HEAD@{2}'
git checkout HEAD@{2} -f

popd 1>/dev/null
popd 1>/dev/null
