#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# (un)install autoreconf
if [ ! -z "$WITH_AUTORECONF" ]; then
    sudo apt-get update
    sudo apt-get install -q dh-autoreconf
else
    sudo apt-get remove -q dh-autoreconf
fi
# install coq
if [ ! -z "$UPDATE_QUICK_DOC" ]; then
    ./install_coq_dot_deps.sh || exit $?
    ./install_doctoc.sh || exit $?
fi
if [ ! -z "$UPDATE_HTML" ]; then
    ./install_proviola.sh || exit $?
fi
./install_coq.sh -prefix /usr/local || exit $?
if [ ! -z "$UPDATE_DEP_GRAPHS" ]; then
    ./make_dpd_graphs.sh || exit $?
fi

popd 1>/dev/null
