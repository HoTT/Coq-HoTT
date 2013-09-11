#!/bin/sh
# pass --disable-bundled-coq to not init the bundled coq repo
if test -d .git && test "x$1" != "x--disable-bundled-coq"
then
    echo "Updating bundled coq..."
    echo " Call '$0 --disable-bundled-coq' to prevent this step from happening."
    echo " To configure without using the bundled Coq, pass --disable-bundled-coq"
    echo " to ./configure"
    git submodule sync
    git submodule update --init --recursive
fi
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
	    git remote add autogen-temp-upstream git://github.com:HoTT/HoTT.git
	    git remote update
	    git checkout autogen-temp-upstream/$BRANCH $FILES
	    if test $? -ne 0
	    then
		echo 'Error: Failed to get autoreconf files.  Try installing autoconf or autoreconf.'
	    fi
	    git remote rm autogen-temp-upstream
	fi
    else
	echo 'Error: autoreconf failed, and you are not using git.  Try installing autoconf or autoreconf.'
    fi
fi
