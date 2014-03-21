#!/usr/bin/env bash

# exit immediately if any command fails
set -e

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

if test ! -d .git
then
    echo 'Error: .git directory does not exist.'
    echo 'This script only works on a git clone of the HoTT repository.'
    exit 1
fi

echo '$ git submodule sync'
git submodule sync
echo '$ git submodule update --init --recursive'
git submodule update --init --recursive

pushd coq-HoTT
echo '$ Patching configure'
if [ ! -z "$(grep '\[ "$MAKEVERSIONMAJOR" -eq 3 -a "$MAKEVERSIONMINOR" -ge 81 \]' configure)" ]
then sed -e 's/\[ "$MAKEVERSIONMAJOR" -eq 3 -a "$MAKEVERSIONMINOR" -ge 81 \]/[ "$MAKEVERSIONMAJOR" -eq 3 -a "$MAKEVERSIONMINOR" -ge 81 -o "$MAKEVERSIONMAJOR" -gt 3 ]/g' \
	 <configure >configure.tmp
     mv configure.tmp configure
     chmod a+x configure
fi
if [ ! -z "$(grep fno-defer-pop configure)" ]
then sed -e 's/-fno-defer-pop//' <configure >configure.tmp
     mv configure.tmp configure
     chmod a+x configure
fi
echo '$ ./configure -local '"$@"
./configure -local "$@"
echo '$ make coqlight coqide'
make coqlight coqide
popd

popd 1>/dev/null
popd 1>/dev/null
