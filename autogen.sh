#!/bin/bash
# pass --with-bundled-coq to init the bundled coq repo
if test "x$1" = "x--with-bundled-coq"
then
    echo "Updating bundled coq..."
    git submodule sync
    git submodule update --init --recursive
else
    COQTOP_OUT="`coqtop -help 2>&1`"
    if test $? -eq 127 || test "$(echo "$COQTOP_OUT" | grep -c -- -indices-matter)" = "0"
    then
        echo "Warning: Could not find a coqtop with a working -indices-matter."
        echo " Call '$0 --with-bundled-coq' to use the bundled version of Coq,"
        echo " or pass the absolute path to coqtop to ./configure via COQBIN."
    fi
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
