#!/usr/bin/env bash

sudo apt-get update -qq
sudo apt-get install -q ghc cabal-install graphviz
cabal update
cabal install graphviz text
