#!/usr/bin/env bash

PS4='$ '

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
