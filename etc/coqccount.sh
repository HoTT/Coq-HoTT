#!/bin/bash

# A script to help determine where there are bottlenecks in the
# parallelization of the build.

# This is a wrapper for coqc that indicates when each coqc process
# starts and stops and the total number of coqc processes running
# at those moments (including the one just about to start and the
# one that is just finishing).  If you run with -j8, you would
# ideally see a lot of 8's in the output.  But note that when
# multiple processes start at once, they often don't count each other.

# When you see smaller numbers transition to larger numbers,
# you can look at which jobs ended just before the transition
# and which jobs started just after the transition, and check
# if the dependencies there are really needed.

# To use this script, do
#   make -jJ COQC=etc/coqccount.sh ...
# or
#   export COQC=etc/coqccount.sh
#   make -jJ ...
# In both cases, fill in J with the number of parallel jobs you want.

# The script sends its output to standard error, so use
# "make ... >file 2>&1" to save it into a file or
# "make ... 2>&1 | command" to pipe it into a command.

# The script uses the pgrep utility to count the number of processes
# named "coqc".  It might seem more sensible to count the coqccount.sh
# processes, but for some reason the same process sometimes shows up
# multiple times, leading to overcounting.

# If the last argument isn't a .v file, we are probably being called
# to determine the Coq version, so just transparently call coqc.
CURFILE="${@: -1}"
if [[ "$CURFILE" != *.v ]]; then
    exec coqc "$@"
fi

# Run coqc in the background, and do our first count a bit after it starts.
# We do it this way rather than adding 1, as it usually allows us to count
# peers that started at about the same time.
coqc "$@" &
sleep 0.001
CNT=`pgrep -cx '^coqc$'`
echo "-> $CNT $CURFILE" >&2

# Do our final count when it ends, and add one for us.
wait $!
RET=$?
CNT=$((`pgrep -cx '^coqc$'` + 1))
echo "<- $CNT $CURFILE" >&2

# We preserve the return value, so that the build stops when there is an error.
exit $RET
