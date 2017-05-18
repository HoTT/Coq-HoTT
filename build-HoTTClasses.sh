#!/usr/bin/env bash

set -x

echo -en 'travis_fold:start:main\\r'

./configure || exit 1
make -j 2

echo -en 'travis_fold:end:main\\r'
