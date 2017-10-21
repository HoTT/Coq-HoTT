#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

if [ -z "$BUILD_COQ" ]
then
    sudo add-apt-repository -y ppa:jgross-h/coq-master-daily
    sudo apt-get update
fi
# (un)install autoreconf
if [ ! -z "$WITH_AUTORECONF" ]; then
    sudo apt-get install -q dh-autoreconf
else
    sudo apt-get remove -q dh-autoreconf
fi
# install coq
if [ ! -z "$UPDATE_QUICK_DOC" ]; then
    ./install_coq_dot_deps.sh
    ./install_doctoc.sh
fi
if [ ! -z "$UPDATE_HTML" ]; then
    ./install_timing_deps.sh
    ./install_proviola.sh
fi
if [ ! -z "$UPDATE_DEP_GRAPHS" ]; then
    ./install_dep_graphs_deps.sh
fi
./install_coq.sh -prefix /usr/local
if [ ! -z "$UPDATE_DEP_GRAPHS" ]; then
    ./make_dpd_graphs.sh
fi

popd 1>/dev/null
