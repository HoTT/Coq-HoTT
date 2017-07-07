#!/usr/bin/env bash

set -x

echo -en 'travis_fold:start:main\\r'

case "$TARGET" in
    "IR")
        USE_IR=""
        ;;
    "trunk" | "8.6")
        USE_IR="--no-ir"
        ;;
    *)
        >&2 echo "Unknown target $TARGET"
        exit 1
        ;;
esac

./configure --hoqdir HoTT --coqbin coq/bin $USE_IR || exit 1
make -j 2

echo -en 'travis_fold:end:main\\r'
