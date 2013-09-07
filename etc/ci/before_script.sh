#!/bin/bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR"

sudo apt-get update -q
sudo apt-get install -q ocaml camlp5 sed grep
if [ ! -z "$WITH_AUTORECONF" ]; then
    sudo apt-get install -q dh-autoreconf
fi

pwd
if [ ! -z "$COQBIN" ]; then
    ./install_coq.sh
fi

popd
