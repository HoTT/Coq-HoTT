#!/usr/bin/env bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

"$DIR"/keep_alive.sh & export PID_KEEP_ALIVE=$!
