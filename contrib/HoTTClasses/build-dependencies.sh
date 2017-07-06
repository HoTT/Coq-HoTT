#!/usr/bin/env bash

############ Caching #############
# Storing cache is handled by travis
# We need to invalidate the cache ourselves

# git ls-remote gets us the desired commit hash

# git rev-parse HEAD gets us the cached one if it exists

# If we need to rebuild we just rm -rf the directory, that way we
# don't deal with historical artefacts

function get_latest {
    git ls-remote --exit-code "$1" "refs/heads/$2" | awk '{print $1}';
}

set -x

echo -en 'travis_fold:start:cache.check\\r'

#NB: always use SkySkimmer/HoTT because I can have PRs not yet merged
#in HoTT/HoTT and ejgallego/HoTT
case "$TARGET" in
    "IR")
        COQ_URL="https://github.com/mattam82/coq.git"
        COQ_BRANCH="IR"
        HOTT_URL="https://github.com/SkySkimmer/HoTT.git"
        HOTT_BRANCH="mz-8.7"
        ;;
    "trunk")
        COQ_URL="https://github.com/coq/coq.git"
        COQ_BRANCH="trunk"
        HOTT_URL="https://github.com/SkySkimmer/HoTT.git"
        HOTT_BRANCH="coq-trunk"
        ;;
    "8.6")
        COQ_URL="https://github.com/coq/coq.git"
        COQ_BRANCH="v8.6"
        HOTT_URL="https://github.com/HoTT/HoTT.git"
        HOTT_BRANCH="master"
        ;;
    *)
        >&2 echo "Unknown target $TARGET"
        exit 1
        ;;
esac

if [ -d coq ];
then
    pushd coq
    LATEST_COQ=$(get_latest "$COQ_URL" "$COQ_BRANCH") || exit 1
    CURRENT_COQ=$(git rev-parse HEAD) || exit 1
    popd
    if [ $LATEST_COQ != $CURRENT_COQ ];
    then
        # we need to rebuild HoTT if Coq is changed
        rm -rf coq HoTT
    fi
fi

if [ -d HoTT ];
then
    pushd HoTT
    LATEST_HOTT=$(get_latest "$HOTT_URL" "$HOTT_BRANCH") || exit 1
    CURRENT_HOTT=$(git rev-parse HEAD)
    popd
    if [ $LATEST_HOTT != $CURRENT_HOTT ];
    then rm -rf HoTT
    fi
fi

echo -en 'travis_fold:end:cache.check\\r'

if [ ! "(" -d coq ")" ]
then
    echo 'Building Coq...'
    echo -en 'travis_fold:start:coq.build\\r'

    git clone --depth 1 -b "$COQ_BRANCH" -- "$COQ_URL" coq || exit 1
    pushd coq
    ./configure -local || exit 1
    make -j 2 tools coqbinaries pluginsopt states || exit 1
    popd

    echo -en 'travis_fold:end:coq.build\\r'
else
    echo "Using cached Coq."
fi

if [ ! "(" -d HoTT ")" ];
then
    echo 'Building HoTT...'
    echo -en 'travis_fold:start:HoTT.build\\r'

    git clone --depth 1 -b "$HOTT_BRANCH" -- "$HOTT_URL" HoTT || exit 1
    pushd HoTT

    # don't let autogen clone some other Coq
    mv .git .git-backup
    ./autogen.sh || exit 1
    mv .git-backup .git

    ./configure COQBIN="$(pwd)/../coq/bin/" || exit 1
    make -j 2 || exit 1
    popd

    echo -en 'travis_fold:end:HoTT.build\\r'
else
    echo "Using cached HoTT."
fi
