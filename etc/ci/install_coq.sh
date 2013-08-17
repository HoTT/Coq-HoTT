#!/bin/bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

if [ -z "$BRANCH" ]; then
    echo '$BRANCH must not be empty'
    exit 1
fi

if [ -z "$COMMITISH" ]; then
    echo '$COMMITISH must not be empty'
    exit 1
fi

sudo apt-get update -q
sudo apt-get install -q ocaml camlp5 dh-autoreconf sed grep

echo '$'" git clone --depth=5 --branch=$BRANCH git://github.com/HoTT/coq.git coq-HoTT"
git clone --depth=5 --branch=$BRANCH git://github.com/HoTT/coq.git coq-HoTT
pushd coq-HoTT
echo '$ git remote update'
git remote update
echo '$'" git checkout $COMMITISH"
git checkout $COMMITISH
echo '$ ./configure -prefix /usr/local -debug -no-native-compiler'
./configure -prefix /usr/local -debug -no-native-compiler
echo '$ make coqlight'
make coqlight
echo '$ sudo make install-coqlight'
sudo make install-coqlight
popd

popd 1>/dev/null
popd 1>/dev/null
