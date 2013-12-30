#!/usr/bin/env python

# This script takes as input the content of the *.aux files for
# The HoTT Book, see https://github.com/HoTT/book/ and processes
# the given *.v file by inserting page and label references into it.

# The script expects the content of *.aux files on stdin. Use like this:
# cat ../book/*.aux | etc/Book.py contrib/HoTTBook.v

import re
import sys
import argparse
from argparse import RawTextHelpFormatter
import shutil
import os

description = """
Process Coq file (e.g. HoTTBook.v) and refresh with respect to the
HoTT book *.aux files. The script expects the content of 
*.aux files on stdandard input. Typical use:

  cat ../book/*.aux | etc/Book.py contrib/HoTTBook.v

"""

# Parse command line arguments
parser = argparse.ArgumentParser(description = description, add_help=True, formatter_class=RawTextHelpFormatter)
parser.add_argument ("--debug", action='store_true', help='Print debugging info', default=False)
parser.add_argument ("--exercises", action='store_true', help='Process exercises', default=False)
parser.add_argument ("file", help='the Coq file that should be processed\n(probably contrib/HoTTBook.v or contrib/HoTTBookExercises.v)')

args = parser.parse_args()

lineno = 0
skipped = 0
badlabel = 0

def log(msg):
    if args.debug: print("Line {0}: {1}".format(lineno, msg))

def warn(msg):
    print("\n **** WARNING: {0}\n".format(msg))

def die(msg):
    print("\n ***** FATAL ERROR: {0}\n".format(msg))
    sys.exit(1)


# Mapping from envirnment names to names
envname = { 
    'axiom' :      'Axiom',
    'chapter' :    'Chapter',
    'cor' :        'Corollary',
    'defn' :       'Definition',
    'equation' :   'Equation',
    'eg' :         'Example',
    'egs' :        'Examples',
    'ex' :         'Exercise',
    'figure' :     'Figure',
    'lem' :        'Lemma',
    'rmk' :        'Remark',
    'section' :    'Section',
    'subsection' : 'Subsection',
    'symindex' :   'Symbol index',
    'table' :      'Table',
    'thm' :        'Theorem'
}

# Set of environment names that are formalizable
formalizable = set(['axiom', 'cor', 'defn', 'eg', 'egs', 'lem', 'thm'])
if args.exercises:
    formalizable = set(['ex'])

# Step 1: Read the standard input and gather entry info into a dictionary
entries = {}

# The regular expression which matches a label line in a *.aux file
r = re.compile(r"\\newlabel{([a-zA-Z0-9:=_-]+)}{{([0-9.]+)}{([0-9]+)}{[^}]*}{([a-z]+)\.[^}]*}{[^}]*}}")

print """Reading content of *.aux files from standard input...
(If you see this press Ctrl-C, read help with --help option, and try agian.)""",

for line in sys.stdin:
    lineno = lineno + 1
    m = r.match(line)
    if m:
        if not m.group(4) in envname:
            warn('unknown environment name {0}, skipping'.format(m.group(4)))
            badlabel = badlabel + 1
            continue
        label = m.group(1)
        number = map(int, m.group(2).split("."))
        page = int(m.group(3))
        typ = envname[m.group(4)]
        if not m.group(4) in formalizable: continue # entry not formalizable, skip
        log ('match: label = {0}, number = {1}, page = {2}, type = {3}'.format(
            label, number, page, typ))
        if label in entries:
            warn ('duplicate label {0} in *.aux files'.format(label))
        entries[label] = { 'number' : number, 'page' : page, 'typ' : typ }
    else:
        skipped = skipped + 1

print "\r {0}".format(" " * 80)

print ("Statistics:\n{0} lines of input\n{1} lines skipped\n{2} labels found\n{3} labels confused me\n".format(lineno,skipped,len(entries), badlabel))

#### Now we munch the file

print ("Reading {0}".format(args.file))

# Read the whole file in one go (doing things line by line is so 1970's)
with open(args.file, "r") as f:
    coqfile = f.read()

# Break it up
(preamble, rest) = re.split(r'^\(\* END OF PREAMBLE \*\)\s*$', coqfile, flags=re.MULTILINE)

snippets = re.split(r'^\s*\(\* =======+ ([A-Za-z0-9:=_-]+) \*\)\s*$', rest, flags=re.MULTILINE)

# Pop the first snippet, as it is just an empty string
snippets.pop(0)

if len(preamble.split()) > 1000:
    die ('Why is the preamble longer than 1000 lines? Parsing error?')

# Put snippets into the entry dictionary
k = 0
while snippets:
    label = snippets.pop(0)
    content = snippets.pop(0)
    if re.search("========", content):
        die ("entry {0} contanins something that looks like a marker, please fix this first.".format(label))
    k = k + 1
    if label not in entries:
        die ('unknown entry {0} found in Coq file, please fix this first.'.format(label))
    if 'content' in entries[label]:
        die ('duplicate entry {0} found in Coq file, please fix this first.'.format(label))
    entries[label]['content'] = content

#### Regenerate the output file
newentry = []

coqfile = preamble + "(* END OF PREAMBLE *)\n"

# Process entries sorted by page number
for label in sorted(entries.keys(),
                    key = lambda k: (entries[k]['page'], entries[k]['number'])):
    entry = entries[label]
    if 'content' in entry:
        # Fix old content
        content = entry['content'].lstrip()
        # Strip the comment on the first line
        content = content[content.index('\n')+1:]
        # Update Book_X_Y_Z
        book = "_".join(map(str,entry['number']))
        content = re.sub('Book_[0-9_]*[0-9]', 'Book_{0}'.format(book), content)
        # It is a common error to write things like Lemma_X_Y_Z instead of Book_X_Y_Z,
        # so we warn about those.
        suspect_names = "|".join(['Axiom',
                                  'Corollary',
                                  'Example',
                                  'Exercise',
                                  'Lemma',
                                  'Remark',
                                  'Theorem'])
        suspect = re.search('({0})_[0-9]*[0-9]'.format(suspect_names), content)
        if suspect:
            better = re.sub('({0})'.format(suspect_names), 'Book', suspect.group(0))
            warn ('You wrote "{0}", should it not be "{1}"?'.format(suspect.group(0), better))
    else:
        # Genereate new content
        content = ''
        newentry.append(label)
    # Put in the correct first line
    content = "(** {0} {1} *)\n\n{2}\n\n".format(
        entry['typ'], '.'.join(map(str,entry['number'])), content.strip())
    coqfile += '(* {0} {1} *)\n{2}'.format('=' * 50, label, content)

if newentry: print ("New entries: {0}".format(newentry))

# Copy the file to backup
k = 1
while os.path.exists("{0}.bak.{1}".format(args.file, k)): k = k + 1
backupfile = "{0}.bak.{1}".format(args.file, k)
print ("Making backup file {0}".format(backupfile))
shutil.move(args.file, backupfile)

# Write out the new file
with open(args.file, 'w') as f:
    f.write(coqfile)

print ("Wrote new version of {0}".format(args.file))
