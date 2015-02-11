#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR" 1>/dev/null

# only make if we should ($UPDATE_QUICK_DOC is not empty) and we're the same as origin/master
if [ -z "$UPDATE_QUICK_DOC" ]; then
    echo 'Not updating TOCs because $UPDATE_QUICK_DOC is not set'
    exit 0
fi

COMMITISH="$(git rev-parse HEAD)"

git reset --hard

"$DIR"/add_upstream.sh

git remote update

echo "Updating TOCs..."
echo '$ ./etc/update-TOCs'
./etc/update-TOCs || exit $?

if [ -z "$(git diff HEAD)" ]; then
    exit 0
fi

"$DIR"/configure_commit.sh
echo '$ git branch -a'
git branch -a
echo '$ git --no-pager diff HEAD'
git --no-pager diff HEAD
echo '$ git --no-pager diff HEAD..origin/master'
git --no-pager diff HEAD..origin/master
echo '$ git --no-pager diff HEAD..upstream/master'
git --no-pager diff HEAD..upstream/master

BAD_REMOTES="$(git remote -v | grep origin | grep -v 'github.com/HoTT/HoTT')"
UPSTREAM_LOG="$(git log HEAD..upstream/master)"
#MASTER_LOG="$(git log HEAD..master)"
#ORIGIN_LOG="$(git log HEAD..origin/master)"

git commit -am "Rebuild TOCs (auto)"
TOCS_COMMIT="$(git rev-parse HEAD)"

# check that we're in the right place, or that we have -f
if [ "$1" != "-f" ]; then
    if [ ! -z "$BAD_REMOTES" ]; then
	echo 'Not updating TOCs because there are remotes which are not HoTT/HoTT:'
	echo "$BAD_REMOTES"
	exit 0
    fi

    # only make the TOCs if we're the same as upstream/master
    if [ ! -z "$UPSTREAM_LOG" ]; then
	echo "Not making TOCs beause we do not match with upstream/master; call '$0 -f' to force"
	exit 0
    fi

#    # only make the TOCs if we're the same as master
#    if [ ! -z "$MASTER_LOG" ]; then
#        echo "Not making TOCs beause we do not match with master; call '$0 -f' to force"
#        exit 0
#    fi
#
#    # only make the TOCs if we're the same as upstream/master
#    if [ ! -z "$ORIGIN_LOG" ]; then
#        echo "Not making TOCs beause we do not match with origin/master; call '$0 -f' to force"
#        exit 0
#    fi
fi

echo '$ git reset --hard'
git reset --hard

echo '$ git rebase origin master && git cherry-pick "'"$TOCS_COMMIT"'" && push_remote.sh HEAD:master'
(git rebase origin master && git cherry-pick "$TOCS_COMMIT" && "$DIR"/push_remote.sh HEAD:master) || (git diff; exit 1)

echo '$ git checkout '"$COMMITISH"
git checkout "$COMMITISH" -f

popd 1>/dev/null
