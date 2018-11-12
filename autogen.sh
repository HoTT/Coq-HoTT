#!/usr/bin/env bash

# don't fall back on git if you interrupt or kill this script
trap "exit 1" SIGINT SIGTERM

if command -v autoreconf >/dev/null 2>&1
then # autoreconf found
    autoreconf -fvi
else
    echo 'Warning: autoreconf not found.  Falling back on git.'
    echo 'This fallback may not work for building older versions of the library.  In that case, try installing autoconf or autoreconf.'
    if test -d .git
    then
	git remote update
	FILES=`cat etc/autoreconf-files`
	BRANCH=`cat etc/autoreconf-branch`
	git checkout $BRANCH $FILES
	if test $? -ne 0 # we failed to find the branch, so try to get it remotely
	then
	    git remote add autogen-temp-upstream git://github.com/HoTT/HoTT.git
	    git remote update
	    git checkout autogen-temp-upstream/$BRANCH $FILES
	    if test $? -ne 0
	    then
		echo 'Error: Failed to get autoreconf files.  Try installing autoconf or autoreconf.'
	    fi
	    git remote rm autogen-temp-upstream
	fi
        git rm --cached $FILES
    else
	echo 'Error: autoreconf failed, and you are not using git.  Try installing autoconf or autoreconf.'
    fi
fi

if [ "$1" != "-skip-submodules" ] && command -v git >/dev/null 2>&1
then # git found
    if test -d .git
    then # we're in a git repository
	git submodule sync # update possibly changed urls
	git submodule update --init --recursive
    elif test ! -d etc/coq-scripts/timing
    then
	echo 'You are not in a git repo; the timing scripts at ./etc/coq-scripts/timing will not be available.'
    fi
elif test ! -d etc/coq-scripts/timing
then
    echo 'You do not have git; the timing scripts at ./etc/coq-scripts/timing will not be available.'
fi
