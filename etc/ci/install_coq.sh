#!/usr/bin/env bash

PS4='$ '
set -ex

# if we're not testing the build of Coq, then install it from debian
if [ -z "$BUILD_COQ" ]
then
    #echo | sudo add-apt-repository ppa:ezyang/coq-git
    #sudo apt-get update -qq
    sudo apt-get install -q coq libcoq-ocaml-dev
    exit 0
fi

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

if test ! -d .git
then
    echo 'Error: .git directory does not exist.'
    echo 'This script only works on a git clone of the HoTT repository.'
    exit 1
fi

echo '$ git submodule sync'
git submodule sync
echo '$ git submodule update --init --recursive'
git submodule update --init --recursive

pushd coq-HoTT
if [ ! -z "$FORCE_COQ_VERSION" ]
then
    git checkout "$FORCE_COQ_VERSION" || exit $?
fi
echo '$ ./configure '"$@"
./configure "$@"
echo '$ make coqlight'
make coqlight
echo '$ sudo make install-coqlight install-devfiles'
sudo make install-coqlight install-devfiles
popd

popd 1>/dev/null
popd 1>/dev/null
