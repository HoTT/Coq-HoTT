#!/usr/bin/python3

# A wrapper for coqc that will try to strip unneeded imports from a file.
# Can be used as
#   path/to/coqcstriprequires.py file.v
# but in order to get the right arguments passed to coqc, it is better to do
#   make COQC=path/to/coqcstriprequires.py file.vo
# or
#   export COQC=path/to/coqcstriprequires.py
#   make ...

# Can be run with -j8 or -j1.  You should adjust the timeout policy
# depending on which case you use.  See below.

# Note that the make process sometimes calls coqc to, e.g., find out the
# Coq version, so we transparently call coqc for such commands.

# Also, stdout is usually redirected to a timing file, so we send all of
# our additional output to stderr.

# Below, file_excludes is set to a list of files to not process.  These are
# summary files, intended to be used to Require multiple other files.

# Also, module_excludes is set to a list of Modules to not try removing.
# We use this to keep "Basics" and "Types" present, by default.

# "Require" and "Require Import" are both handled, but not "Require Export".

# Limitations:
# - Doesn't know about comments.
# - Won't handle a "Require Import" that occurs on the same line as
#   (but after) the period from a previous "Require Import".
# - If the "Require Import" command spans multiple lines and all
#   imports are removed, the result won't be syntactically valid.
# - It would probably be cleaner to just treat the input as a single string
#   rather than working line by line.

import subprocess
import sys
import os
import time
import re

# You can choose a fixed timeout or a dynamic timeout.
# The former is better for runs with -j8, or any time you don't
# trust the timing measurements.
# The latter is best run with -j1 to have more stable timings,
# as it will exclude changes that slow things down.

# Some kind of timeout is important.  For example,
# Classes/implementations/natpair_integers.v and Classes/theory/rationals.v
# both spin when certain lines are removed.
# On my system, the slowest file takes 5.5s usually, so a fixed timeout
# of 10s timeout is fine, but on a slower system you'll need to increase it.

# You can also use a dynamic timeout.  This will ensure that no change
# is accepted if it increases the time to the value given, where
# duration is the best time seen so far.  The reason for the displayed
# formula is to allow for variation in the timing.  In one test, with
# max(duration+0.005, duration*1.03), only around 16 changes were
# aborted due to the timeout, and only a few of those would have succeeded.
# One important one to exclude is Basics from Algebra/.../PullbackFiberSequence,
# as removing that Import really does slow things down a lot.

# Set your timeout policy, in seconds:

def calc_timeout(duration): return max(duration+0.005, duration*1.03)

#def calc_timeout(duration): return 10

# time.perf_counter is better than time.time, since the latter is
# affect by changes to the system clock.  Both return a floating point
# value in seconds.
timer = time.perf_counter

# The default timeout value here will be used for the first run.
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
    return cp.returncode, timer() - start

# Join words with spaces, ignoring None.
def myjoin(words):
    return ' '.join(word for word in words if word is not None)

# The various types of Require commands.  Match group 2 is the
# actual text of the command.
require        = re.compile(r'(^|\s)(Require)($|\s)')
require_import = re.compile(r'(^|\s)(Require Import)($|\s)')
require_export = re.compile(r'(^|\s)(Require Export)($|\s)')

# The period that marks the end of a Require Import command.
period = re.compile(r'[.]\s')

# Files to not strip.  Most of these files are "summary" files that
# Require other files for convenience.  A couple are excluded for
# other reasons, as the comments mention.
file_excludes=[
    'theories/Categories.v',
    'theories/Categories/Adjoint.v',
    'theories/Categories/Adjoint/Composition.v',
    'theories/Categories/Adjoint/Notations.v',
    'theories/Categories/Adjoint/Functorial.v', # breaks Categories/Adjoint.v
    'theories/Categories/Category.v',
    'theories/Categories/Category/Notations.v',
    'theories/Categories/Category/Sigma.v',
    'theories/Categories/Comma.v',
    'theories/Categories/ExponentialLaws.v',
    'theories/Categories/ExponentialLaws/Law1.v',
    'theories/Categories/ExponentialLaws/Law2.v',
    'theories/Categories/ExponentialLaws/Law3.v',
    'theories/Categories/ExponentialLaws/Law4.v',
    'theories/Categories/Functor.v',
    'theories/Categories/Functor/Composition.v',
    'theories/Categories/Functor/Composition/Functorial.v',
    'theories/Categories/Functor/Notations.v',
    'theories/Categories/Functor/Pointwise.v',
    'theories/Categories/Functor/Prod.v',
    'theories/Categories/FunctorCategory.v',
    'theories/Categories/FunctorCategory/Notations.v',
    'theories/Categories/Grothendieck.v',
    'theories/Categories/Grothendieck/ToSet.v',
    'theories/Categories/GroupoidCategory.v',
    'theories/Categories/InitialTerminalCategory.v',
    'theories/Categories/KanExtensions.v',
    'theories/Categories/LaxComma.v',
    'theories/Categories/Limits.v',
    'theories/Categories/NaturalTransformation.v',
    'theories/Categories/NaturalTransformation/Composition.v',
    'theories/Categories/NaturalTransformation/Dual.v',
    'theories/Categories/NaturalTransformation/Notations.v',
    'theories/Categories/Notations.v',
    'theories/Categories/Profunctor.v',
    'theories/Categories/Profunctor/Notations.v',
    'theories/Categories/Pseudofunctor.v',
    'theories/Categories/SetCategory.v',
    'theories/Categories/Structure.v',
    'theories/Categories/Utf8.v',
    'theories/Classes/tests/ring_tac.v',        # slow, and nothing changes
    'theories/Classes/interfaces/integers.v',   # only a comment changes
    ]

module_excludes = ['Basics', 'Types']

def striprequires(vfile):
    changes = 0
    attempts = 0
    timeouts = 0

    # Ensure that the file builds with no changes:
    ret, duration = coqc(False)
    # Exit immediately if it fails, or if the file is excluded from further treatment.
    if ret != 0 or vfile in file_excludes:
        return ret, changes, attempts, timeouts

    with open(vfile, 'r', encoding="utf-8") as f:
        lines = f.readlines()
    os.rename(vfile, vfile+'.bak')

    continuation = False
    for i in range(len(lines)):
        line = lines[i]

        # continued: we are not the first line
        # continuation: we are not the last line
        continued = continuation
        continuation = False
        if continued:
            # A previous line had "Require" or "Require Import" and we didn't find the period yet.
            pos = 0
            start = 0
        else:
            m = require_import.search(line)
            if not m:
                m = require_export.search(line)
                if m:
                    # We don't strip any Require Export lines.
                    continue
                m = require.search(line)
                if not m:
                    # No "Require" of any kind found.
                    continue
            pos, start = m.span(2)
            # pos is where the "R" in "Require" is; start is the first character after
            # the full command ("Require" or "Require Import").

        # Preserve any space characters after the starting position, e.g. indentation:
        while start < len(line) and line[start] == ' ':
            start += 1
        if start >= len(line):
            # No imports or period on this line:
            continutation = True
            continue

        end = period.search(line, pos=start)
        if end:
            end = end.start() # The position of the period
        else:
            # No period found
            continuation = True
            end = len(line)-1 # The position of the newline character

        imports = line[start:end].split()
        for j in range(len(imports)):
            save = imports[j]
            if save in module_excludes: continue
            attempts += 1
            imports[j] = None
            newimports = myjoin(imports)
            if newimports or continuation or continued:
                lines[i] = line[:start] + newimports + line[end:]
            else:
                # Completely drop the Require Imports section of the line, including period:
                lines[i] = line[:pos] + line[end+1:]
            fixprev = None
            if lines[i].strip() == '':
                # If the resulting line is empty, remove it completely:
                lines[i] = ''
            elif lines[i].strip() == '.':
                # Avoid having a line with just a period.
                fixprev = i-1
                while fixprev >= 0 and lines[fixprev] == '': fixprev -= 1
                assert(fixprev >= 0)
                assert(lines[fixprev][-1] == '\n')
                lines[fixprev] = lines[fixprev][:-1] + '.\n'
                lines[i] = ''

            with open(vfile, 'w', encoding="utf-8") as f:
                f.write(''.join(lines))
            ret, newduration = coqc(True, timeout=calc_timeout(duration))

            if ret == 0:
                changes += 1
                duration = newduration
            else:
                imports[j] = save
                lines[i] = line[:start] + myjoin(imports) + line[end:]
                if fixprev is not None:
                    # Remove the period we added:
                    assert(lines[fixprev][-2:] == '.\n')
                    lines[fixprev] = lines[fixprev][:-2] + '\n'
                if ret == 1111:
                    timeouts += 1

        if None not in imports:
            # Use the saved line, to preserve whitespace:
            lines[i] = line

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

    vfile = vfiles[0]

    ret, changes, attempts, timeouts = striprequires(vfile)

    if changes > 0:
        print('>>> %2d  changes made to %s' % (changes, vfile), file=sys.stderr)
    if attempts > 0:
        print('--- %2d attempts made to %s' % (attempts, vfile), file=sys.stderr)
    if timeouts > 0:
        print('ttt %2d timeouts for %s' % (timeouts, vfile), file=sys.stderr)

    sys.exit(ret)
