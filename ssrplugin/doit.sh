#!/bin/bash
# This is how you can compile ssrplugin with HoTT
# First we make the new Coq standard library (you did run ./configure, right?)
make -C .. stdlib
# Then we make the dynamic library
export COQBIN=$HOME/Documents/project/homotopy/coq/bin/
export PATH=$COQBIN:$PATH
# We replace the standard Coq with the HoTT version
COQC=../hoqc make all

