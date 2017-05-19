#!/usr/bin/env bash

set -x

echo -en 'travis_fold:start:main\\r'

case "$TARGET" in
    "IR")
        USE_IR="YES_IR"
        ;;
    "trunk" | "8.6")
        USE_IR="NO_IR"
        ;;
    *)
        >&2 echo "Unknown target $TARGET"
        exit 1
        ;;
esac

./configure "$USE_IR" || exit 1
make -j 2

echo -en 'travis_fold:end:main\\r'
