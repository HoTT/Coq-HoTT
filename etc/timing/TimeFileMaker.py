#!/usr/bin/python
from __future__ import with_statement
import os, sys, re

# This is a helper script for make-pretty-timed.sh and
# make-pretty-timed-diff.sh.

# This script parses the output of `make TIMED=1` into a dictionary
# mapping names of compiled files to the number of minutes and seconds
# that they took to compile.

STRIP_REG = re.compile('^(coq/|contrib/|)(?:theories/)?')
STRIP_REP = r'\1'

def get_times(file_name):
    '''
    Reads the contents of file_name, which should be the output of
    'make TIMED=1', and parses it to construct a dict mapping file
    names to compile durations, as strings.  Removes common prefixes
    using STRIP_REG and STRIP_REP.
    '''
    with open(file_name, 'r') as f:
        lines = f.read()
    reg = re.compile(r'^([^ ]*) \(user: ([0-9\.]+) mem: [0-9]+ [a-zA-Z]+\)$', re.MULTILINE)
    times = reg.findall(lines)
    times_dict = {}
    if all(STRIP_REG.search(name) for name, time in times):
        times = tuple((STRIP_REG.sub(STRIP_REP, name), time) for name, time in times)
    for name, time in times:
        seconds, milliseconds = time.split('.')
        seconds = int(seconds)
        minutes, seconds = int(seconds / 60), seconds % 60
        times_dict[name] = '%dm%02d.%ss' % (minutes, seconds, milliseconds)
    return times_dict

def get_sorted_file_list_from_times_dict(times_dict, descending=True):
    '''
    Takes the output dict of get_times and returns the list of keys,
    sorted by duration.
    '''
    def get_key(name):
        minutes, seconds = times_dict[name].replace('s', '').split('m')
        return (int(minutes), float(seconds))
    return sorted(times_dict.keys(), key=get_key, reverse=descending)

def to_seconds(time):
    '''
    Converts a string time into a number of seconds.
    '''
    minutes, seconds = time.replace('s', '').split('m')
    sign = -1 if time[0] == '-' else 1
    return int(minutes) * 60 + float(seconds)

def from_seconds(seconds, signed=False):
    '''
    Converts a number of seconds into a string time.
    '''
    sign = ('-' if seconds < 0 else '+') if signed else ''
    seconds = abs(seconds)
    minutes = int(seconds) / 60
    seconds -= minutes * 60
    full_seconds = int(seconds)
    partial_seconds = int(100 * (seconds - full_seconds))
    return sign + '%dm%02d.%02ds' % (minutes, full_seconds, partial_seconds)

def sum_times(times, signed=False):
    '''
    Takes the values of an output from get_times, parses the time
    strings, and returns their sum, in the same string format.
    '''
    return from_seconds(sum(map(to_seconds, times)), signed=signed)
