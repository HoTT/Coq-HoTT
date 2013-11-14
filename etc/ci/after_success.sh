#!/bin/bash

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# only make if we should ($UPDATE_HTML is not empty) and we're the same as origin/master
if [ ! -z "$UPDATE_HTML" ]; then
    git remote update
    if [ -z "$(git diff origin/master)" ]; then
        # make the html and push it, if we should
        ./generate_and_push_doc.sh
        ./autogen_and_push.sh
    fi
fi

popd 1>/dev/null
