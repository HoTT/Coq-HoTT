#!/usr/bin/env bash

set -x

./configure || exit 1
make -j 2
