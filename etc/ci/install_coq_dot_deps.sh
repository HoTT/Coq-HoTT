#!/usr/bin/env bash

sudo apt-get update -q
sudo apt-get install -q haskell-cabal-install cabal-install
cabal update
