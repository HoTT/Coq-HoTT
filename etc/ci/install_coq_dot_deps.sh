#!/usr/bin/env bash

PS4='$ '
set -x

# http://unix.stackexchange.com/questions/82598/how-do-i-write-a-retry-logic-in-script-to-keep-retrying-to-run-it-upto-5-times
n=0
until [ $n -ge 10 ]
do
    cabal update && break
    n=$[$n+1]
    sleep 10
done
cabal install graphviz-2999.18.0.2 text || \
    (cabal install graphviz-2999.18.0.2 &&
            cabal install text) || exit $?
