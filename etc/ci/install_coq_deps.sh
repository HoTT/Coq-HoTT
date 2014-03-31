#!/usr/bin/env bash

PS4='$ '
set -x

#sudo apt-get update -qq
sudo apt-get install -q sed grep wget tar xsltproc mercurial python-lxml python-pexpect libxml2-dev libxslt1-dev
if [ ! -z "$BUILD_COQ" -o ! -z "$UPDATE_DEP_GRAPHS" ]
then
    sudo apt-get install -q ocaml camlp5
fi
