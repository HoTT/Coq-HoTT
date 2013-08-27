#!/bin/bash

sudo apt-get update -q
sudo apt-get install -q ocaml camlp5 sed grep
if [ ! -z "$WITH_AUTORECONF" ]; then
    sudo apt-get install -q dh-autoreconf
fi
