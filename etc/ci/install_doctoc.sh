#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR" 1>/dev/null

# Stop npm from failing
sudo -E npm config set strict-ssl false

# Update npm
sudo -E npm i -g npm

sudo -E npm install -g doctoc || exit $?

popd 1>/dev/null
