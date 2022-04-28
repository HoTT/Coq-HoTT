#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# install autoreconf
sudo apt-get update
sudo apt-get install -q autoconf

# install coq
if [ ! -z "$UPDATE_QUICK_DOC" ]; then
    ./install_coq_dot_deps.sh || exit $?
    ./install_doctoc.sh || exit $?
fi
if [ ! -z "$UPDATE_HTML" ]; then
    ./install_proviola.sh || exit $?
fi

popd 1>/dev/null
