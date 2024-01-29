#!/usr/bin/python3

# A wrapper for coqc that will try to replace a regular expression
# with a replacement string.  The results need to be inspected by
# hand, as it will often be too eager.  See the "Limitations" section
# below.

# The patterns are specified using environment variables, using python's
# regular expression syntax, e.g.:
#   export COQC_SEARCH='(^|[^n])(refine|rapply)'
#   export COQC_REPLACE='\1n\2'
# This will replace an occurence of 'refine' or 'rapply' that is either
# at the start of the line or preceeded by a character other than 'n'
# with the same thing with an 'n' inserted.  '\1' and '\2' refer to
# the parts of the input line that matched the expressions in parentheses.
# - COQC_SEARCH is matched against each *line* of the file separately,
#   not including newlines.
# - Matches are replaced one at a time, from left to right, and each one
#   is tested and kept only if the file builds successfully and meets the
#   timing constraint.
# - After a replacement, the line is scanned for the next match that
#   starts *after* that replacement string.
# - After a failed replacement, the string is scanned for the next match
#   that starts one character to the right of the last match, allowing
#   for overlapping matches.
# - Lines containing 'noreplace' are left as is.  This can be put in as
#   a temporary marker inside a comment.
# Other examples:
#   export COQC_SEARCH='\W*`{Univalence}'
#   export COQC_REPLACE=''
#
#   export COQC_SEARCH='(Truncations|Spaces\.Nat|Spaces\.Pos|Spaces\.Int|Spaces\.No|Pointed|Homotopy.Join|Homotopy.HSpace|WildCat|Algebra.AbSES)'
#   export COQC_REPLACE='\1.Core'
# Search for "min(20" below for how to restrict this to the start of each file.

# Can be used as
#   path/to/coqcreplace.py path/tofile.v
# but in order to get the right arguments passed to coqc, it is better to do
#   make COQC=path/to/coqcreplace.py path/tofile.vo
# or
#   export COQC=path/to/coqcreplace.py
#   make file.vo
# To run on the whole library, avoiding test/ and contrib/, can do:
#   export COQC=path/to/coqcreplace.py
#   make clean; make -j<fill in> theories/HoTT.vo theories/Categories.vo
# Use "unset COQC" when done.

# You'll need to also adjust the timing policy.  See below.

# Can be run with -j<#cores> or -j1.  Timing is more accurate with -j1.

# Note that the make process sometimes calls coqc to, e.g., find out the
# Coq version, so we transparently call coqc for such commands.

# Also, stdout is usually redirected to a timing file, so we send all of
# our additional output to stderr.

# Below, file_excludes is set to a list of files to not process.  Not sure
# if this is needed.

# Limitations:
# - Doesn't know about comments.
# - Shouldn't be run on test/ folder, as many definitions there are preceded
#   with "Fail".
# - It's possible that a change (e.g. to a tactic) doesn't cause a file to fail,
#   but causes a *later* file to fail.  Currently the only work-around is to
#   add the first file to the file_excludes list below, or to mark the
#   problematic line with "noreplace".

import subprocess
import sys
import os
import time
import re

# You can choose a fixed timeout or a dynamic timeout.
# For this script, you probably always want a dynamic timeout.
# A change is only accepted if the new time is <= the time given
# by the formula, where duration is the best time seen so far.

# Set your timeout policy, in seconds:

# This policy only accepts changes that make at least a small
# improvement to the timing.  This is appropriate for changes that are
# intended to improve build speed.  But note that there are random
# fluctuations, so this will also accept changes that are neutral.
# The second part, duration*0.9, is there just to ensure that the
# return value is always positive.

#def calc_timeout(duration): return max(duration-0.03, duration*0.9)

# If changes have other benefits, e.g. reducing dependencies, and are
# very unlikely to increase the build time, then you might want to
# accept them even if the time increases slightly, to account for
# timing noise.

def calc_timeout(duration): return max(duration+0.1, duration*1.05)

# time.perf_counter is better than time.time, since the latter is
# affected by changes to the system clock.  Both return a floating point
# value in seconds.
timer = time.perf_counter

# The default timeout value here will be used for the first run.
# Returns (exit code of coqc, elapsed time).  If the elapsed time
# is greater than the timeout, returns (1111, elapsed time).
def coqc(quiet=False, timeout=60):
    start = timer()
    try:
        if quiet:
            cp = subprocess.run(['coqc'] + sys.argv[1:], timeout=timeout,
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        else:
            cp = subprocess.run(['coqc'] + sys.argv[1:], timeout=timeout)
    except subprocess.TimeoutExpired:
        return 1111, timer() - start
    # subprocess.run uses a busy loop to check the timeout, so it may allow
    # the command to run longer than the limit.  So we also check here.
    elapsed = timer() - start
    if elapsed > timeout:
        return 1111, elapsed
    else:
        return cp.returncode, elapsed

# Files to not process, e.g. summary files, files defining tactics used elsewhere, etc.
file_excludes=[
    ]

# Given a match object match, a replacement string (which can include \1, etc),
# and the string s that was searched, return string with the replacement done.
def replace_match(match, replace, s):
    return s[:match.start()] + match.expand(replace) + s[match.end():]

def replace(vfile):
    changes = 0
    attempts = 0
    timeouts = 0

    # Ensure that the file builds with no changes:
    ret, duration1 = coqc(False)
    # Exit immediately if it fails, or if the file is excluded from further treatment.
    if ret != 0 or vfile in file_excludes:
        return ret, changes, attempts, timeouts

    # Do a second run to get a more stable duration value:
    ret2, duration2 = coqc(False)
    duration = (duration1 + duration2)/2.0

    with open(vfile, 'r', encoding="utf-8") as f:
        lines = f.readlines()
    os.rename(vfile, vfile+'.bak')

    # Replace len(lines) with min(20, len(lines)) to only look for matches in first 20 lines:
    for i in range(len(lines)):
        # Save last successful line; we'll modify lines[i]:
        line = lines[i]

        # Don't make changes to lines with this tag:
        if 'noreplace' in line: continue

        end = len(line)
        # Exclude carriage return and newline from search:
        while end > 0 and line[end-1] in '\n\r': end -= 1
        start = 0

        while True:
            # Note: When start > 0, '^' will never match;  but '$' does match endpos
            match = coqc_search.search(lines[i], pos=start, endpos=end)
            if not match:
                break
            lines[i] = replace_match(match, coqc_replace, lines[i])
            
            attempts += 1
            with open(vfile, 'w', encoding="utf-8") as f:
                f.write(''.join(lines))
            ret, newduration = coqc(True, timeout=calc_timeout(duration))

            if ret == 0:
                start = match.end()
                changes += 1
                duration = newduration
            else:
                lines[i] = line
                start = match.start() + 1
                if ret == 1111:
                    timeouts += 1

    if changes == 0:
        # Get rid of the backup file if we made no changes:
        os.rename(vfile+'.bak', vfile)
        if attempts > 0:
            # Ensure we are in a consistent state:
            ret, _ = coqc(True)
    else:
        # We only need to do an extra run if the last one failed:
        if ret != 0:
            with open(vfile, 'w', encoding="utf-8") as f:
                f.write(''.join(lines))
            ret, _ = coqc()

    return ret, changes, attempts, timeouts

if __name__ == '__main__':
    vfiles = [arg for arg in sys.argv if arg.endswith('.v')]

    if len(vfiles) == 0:
        # We are called for some other reason.  Just call coqc and exit.
        sys.exit(coqc()[0])
    elif len(vfiles) > 1:
        print('!!! Called with more than one vfile???', file=sys.stderr)
        sys.exit(coqc()[0])

    # These will give errors if the environment variables are not set:
    coqc_search = re.compile(os.environ['COQC_SEARCH'])
    coqc_replace = os.environ['COQC_REPLACE']

    vfile = vfiles[0]

    ret, changes, attempts, timeouts = replace(vfile)

    if changes > 0:
        print('>>> %2d  changes made to %s' % (changes, vfile), file=sys.stderr)
    if attempts > 0:
        print('--- %2d attempts made to %s' % (attempts, vfile), file=sys.stderr)
    if timeouts > 0:
        print('ttt %2d timeouts for %s' % (timeouts, vfile), file=sys.stderr)

    sys.exit(ret)
