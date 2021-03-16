#!/usr/bin/env bash

PS4='$ '
set -x

# http://unix.stackexchange.com/questions/82598/how-do-i-write-a-retry-logic-in-script-to-keep-retrying-to-run-it-upto-5-times
n=0
until [ $n -ge 10 ]
do
    cabal v1-update && break
    n=$[$n+1]
    sleep 10
done
cabal v1-install graphviz text
