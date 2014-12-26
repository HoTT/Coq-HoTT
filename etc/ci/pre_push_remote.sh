#!/usr/bin/env bash

PS4='$ '
set +x

if [ -z "$OAUTH_TOKEN" ]; then
    echo 'Error: Not pushing because $OAUTH_TOKEN is empty'
    exit 1
fi

echo "Updating ~/.netrc file"
echo >> ~/.netrc
echo "machine github.com login $OAUTH_TOKEN" >> ~/.netrc
