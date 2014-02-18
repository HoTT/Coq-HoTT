#!/usr/bin/env bash

sudo apt-get update -q
sudo apt-get install -q ghc cabal-install graphviz
cabal update
cabal install graphviz text
