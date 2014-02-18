#!/usr/bin/env bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

sudo apt-get update -q
# (un)install autoreconf
if [ ! -z "$WITH_AUTORECONF" ]; then
    sudo apt-get install -q dh-autoreconf
else
    sudo apt-get remove -q dh-autoreconf
fi
# install time for make `TIMED=1`
sudo apt-get install -q time
# install coq
./install_coq_deps.sh
./install_coq_dot_deps.sh
./install_proviola.sh
./install_coq.sh -prefix /usr/local -debug

popd 1>/dev/null
