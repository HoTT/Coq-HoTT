#!/usr/bin/env bash

# exit immediately if you interrupt or kill this script
trap "exit 1" SIGHUP SIGINT SIGTERM

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
pushd "$DIR" 1>/dev/null || exit 1

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null || exit 1

if test ! -d .git
then
    echo 'Error: .git directory does not exist.'
    echo 'This script only works on a git clone of the HoTT repository.'
    exit 1
fi

echo '$ git submodule sync'
git submodule sync || exit 1
echo '$ git submodule update --init --recursive'
git submodule update --init --recursive || exit 1

pushd coq-HoTT || exit 1
echo '$ ./configure -local '"$@"
./configure -local "$@" || exit 1
echo '$ make coqlight coqide'
make coqlight coqide
if [ $? -ne 0 ]
then
    echo "make failed; cleaning the directory and trying again"
    sleep 3
    git clean -xfd || echo 'WARNING: Cleaning failed'
    git reset --hard || echo 'WARNING: Cleaning failed'
    echo '$ ./configure -local '"$@"
    ./configure -local "$@" || exit 1
    echo '$ make coqlight coqide'
    make coqlight coqide || exit 1
fi
popd

# now clean the HoTT repository, so that we don't have inconsistent compiled files
echo '$ make clean'
make clean

popd 1>/dev/null
popd 1>/dev/null
