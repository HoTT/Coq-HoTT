#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

# don't leak the OAUTH Token
set +x

if [ -z "$OAUTH_TOKEN" ]; then
    echo 'Error: Not pushing because $OAUTH_TOKEN is empty'
    exit 1
fi

echo "Updating ~/.netrc file"
echo >> ~/.netrc
echo "machine github.com login $OAUTH_TOKEN" >> ~/.netrc
set -x

"$DIR"/configure_commit.sh

REPO="$(git remote -v | grep -o 'origin\s\+\(.*\?\)\s\+(push)' | sed s'/origin\s\+//g' | sed s'/\s\+(push)//g' | sed s'#git://github.com/#https://github.com/#g')"

echo '$ git push '"$REPO ""$@"
git push $REPO "$@"

popd 1>/dev/null
popd 1>/dev/null
