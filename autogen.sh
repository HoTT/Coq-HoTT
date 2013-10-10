#!/bin/sh

# don't fall back on git if you interrupt or kill this script
trap "exit 1" SIGINT SIGTERM

autoreconf -fvi
if test $? -eq 127
then
    echo 'Warning: autoreconf not found.  Falling back on git.'
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
