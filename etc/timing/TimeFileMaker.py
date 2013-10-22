#!/usr/bin/python
from __future__ import with_statement
import os, sys, re

STRIP_REG = re.compile('^(|coq/)theories/')
STRIP_REP = r'\1'

def get_times(file_name):
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
    def get_key(name):
        minutes, seconds = times_dict[name].replace('s', '').split('m')
        return (int(minutes), float(seconds))
    return sorted(times_dict.keys(), key=get_key, reverse=descending)

def sum_times(times):
    def to_seconds(time):
        minutes, seconds = time.replace('s', '').split('m')
        return int(minutes) * 60 + float(seconds)
    seconds = sum(map(to_seconds, times))
    minutes = int(seconds) / 60
    seconds -= minutes * 60
    full_seconds = int(seconds)
    partial_seconds = int(100 * (seconds - full_seconds))
    return '%dm%02d.%02ds' % (minutes, full_seconds, partial_seconds)
