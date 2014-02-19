#!/usr/bin/env bash

PS4='$ '
set -x

sudo apt-get update -qq
sudo apt-get install -q sed grep wget tar xsltproc mercurial python-lxml python-pexpect libxml2-dev libxslt1-dev ocaml camlp5
