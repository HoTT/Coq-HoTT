#!/usr/bin/env python

# This script takes as input the content of the *.aux files for
# The HoTT Book, see https://github.com/HoTT/book/ and processes
# the given *.v file by inserting page and label references into it.

# The script expects the content of *.aux files on stdin. Use like this:
# cat ../book/*.aux | etc/Book.py contrib/HoTTBook.v

import re
import sys
import argparse
import shutil
import os

# Parse command line arguments
parser = argparse.ArgumentParser(description = "Munch HoTTBook.v")
parser.add_argument ("--debug", action='store_true', help='Print debugging info', default=False)
parser.add_argument ("file", help='the Coq file that should be processed')

args = parser.parse_args()

lineno = 0
skipped = 0
badlabel = 0

def log(msg):
    if args.debug: print("Line {0}: {1}".format(lineno, msg))

def warn(msg):
    print("WARNING: {0}".format(msg))

def die(msg):
    print("FATAL ERROR: {0}".format(msg))
    sys.exit(1)


# Mapping from envirnment names to names, and flag indicating whether it is formalizable
envname = { 
    'chapter' :    ('Chapter', False),
    'cor' :        ('Corollary', True),
    'defn' :       ('Definition', True),
    'equation' :   ('Equation', False),
    'eg' :         ('Example', True),
    'egs' :        ('Examples', True),
    'ex' :         ('Exercise', True),
    'figure' :     ('Figure', False),
    'lem' :        ('Lemma', True),
    'rmk' :        ('Remark', False),
    'section' :    ('Section', False),
    'subsection' : ('Subsection', False),
    'table' :      ('Table', False),
    'thm' :        ('Theorem', True)
}

# Step 1: Read the standard input and gather entry info into a dictionary
entries = {}

# The regular expression which matches a label line in a *.aux file
r = re.compile(r"\\newlabel{([a-zA-Z0-9:=_-]+)}{{([0-9.]+)}{([0-9]+)}{[^}]*}{([a-z]+)\.[^}]*}{[^}]*}}")

for line in sys.stdin:
    lineno = lineno + 1
    m = r.match(line)
    if m:
        if not m.group(4) in envname:
            warn('unknown environment name {0}, skipping'.format(m.group(4)))
            badlabel = badlabel + 1
            continue
        label = m.group(1)
        number = m.group(2)
        page = int(m.group(3))
        typ = envname[m.group(4)]
        if not typ[1]: continue # entry not formalizable, skip
        log ('match: label = {0}, number = {1}, page = {2}, type = {3}'.format(label, number, page, typ[0]))
        if label in entries:
            warn ('duplicate label {0} in *.aux files'.format(label))
        entries[label] = { 'number' : number, 'page' : page, 'typ' : typ[0] }
    else:
        skipped = skipped + 1

print ("\nStatistics:\n{0} lines of input\n{1} lines skipped\n{2} labels found\n{3} labels confused me\n".format(lineno,skipped,len(entries), badlabel))

#### Now we munch the file

print ("Reading {0}".format(args.file))

# Read the whole file (line by line processing is so 1970's)
with open(args.file, "r") as f:
    coqfile = f.read()

# Break it up
snippets = re.split(r'^\s*\(\* =======+ ([A-Za-z0-9:=_-]+) \*\)\s*$', coqfile, flags=re.MULTILINE)

# Get the preamble
preamble = snippets.pop(0)

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

print ("Found {0} labels in the Coq file".format(k))

#### Regenerate the output file
newentry = []

coqfile = preamble + "\n"

# Process entries sorted by page number
for label in sorted(entries.keys(), key = lambda k: (entries[k]['page'], entries[k]['number'])):
    entry = entries[label]
    if 'content' in entry:
        # Fix old content
        content = entry['content'].lstrip()
        # Strip the comment on the first line
        content = content[content.index('\n')+1:]
        # Update Book_X_Y_Z
        book = "_".join(entry['number'].split("."))
        content = re.sub('Book_[0-9_]*[0-9]', 'Book_{0}'.format(book), content)
    else:
        # Genereate new content
        content = ''
        newentry.append(label)
    # Put in the correct first line
    content = "(* {0} {1}, page {2} *)\n\n{3}\n\n".format(entry['typ'], entry['number'], entry['page'], content.strip())
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
