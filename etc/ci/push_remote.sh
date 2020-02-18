#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

# Don't leak secrets
set +x
if [ ! -z "$OAUTH_TOKEN" ]; then
    echo "Updating ~/.netrc file"
    echo >> ~/.netrc
    echo "machine github.com login $OAUTH_TOKEN" >> ~/.netrc
elif [ ! -z "$ACTIONS_DEPLOY_KEY" ]; then
    echo "Updating ~/.ssh/id_rsa"
    echo "$ACTIONS_DEPLOY_KEY" > ~/.ssh/id_rsa
else
    echo 'Error: Not pushing because $OAUTH_TOKEN and $ACTIONS_DEPLOY_KEY are empty'
    exit 0
fi
set -x

echo "Configuring git for commit"
if [ -z "$(git config --global user.name)" ]; then
    git config --global user.name "CI Bot"
fi
if [ -z "$(git config --global user.email)" ]; then
    git config --global user.email "CI-Bot@fake.fake"
fi

REPO="$(git remote -v | grep -o 'origin\s\+\(.*\?\)\s\+(push)' | sed s'/origin\s\+//g' | sed s'/\s\+(push)//g' | sed s'#git://github.com/#https://github.com/#g')"

echo '$ git push '"$REPO ""$@"
git push $REPO "$@" || exit $?

popd 1>/dev/null
popd 1>/dev/null
