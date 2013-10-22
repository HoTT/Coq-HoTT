#!/bin/bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root; use `cd` so we only need one `popd`
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"
