#!/usr/bin/env bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

pip install lxml pexpect-u

# wget -N http://mws.cs.ru.nl/proviola/files/proviola.tar.gz
# we need one that works with `coqdoc --utf8`.  Neither the .tar.gz nor the latest sources do, but the .tar.gz is closer.  So use a slightly patched version.
if [ -d proviola ]
then
    (cd proviola && git pull)
    #(cd proviola && hg up)
else
    git clone https://github.com/JasonGross/proviola-source proviola
    #hg clone https://bitbucket.org/Carst/proviola-source proviola
fi


#PYTHON_VERSION="$(python --version 2>&1)"
#case "$PYTHON_VERSION" in
#    "Python 2.7"*)
#	# supported python
#	;;
#    "Python 2.6"*)
#	echo "Downloading argparse, which isn't in $PYTHON_VERSION"
#	wget -N http://argparse.googlecode.com/files/argparse-1.2.1.tar.gz
#	if [ -d argparse-1.2.1 ]
#	then
#	    rm -r argparse-1.2.1
#	fi
#	tar -xzvf argparse-1.2.1.tar.gz
#	cp argparse-1.2.1/argparse.py proviola/camera/
#	;;
#    *)
#	echo "WARNING: Unsupported python version '$PYTHON_VERSION'"
#esac

popd 1>/dev/null
popd 1>/dev/null
