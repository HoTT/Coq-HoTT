#!/usr/bin/python
from __future__ import with_statement
import os, sys, re
from TimeFileMaker import *

# This is a helper script for make-pretty-timed-diff.sh.

# This uses TimeFileMaker.py to format timing information.

def make_table_string(left_times_dict, right_times_dict,
                      descending=True,
                      left_tag="After", right_tag="Before"):
    # We first get the names of all of the compiled files: all files
    # that were compiled either before or after.
    all_names_dict = dict()
    all_names_dict.update(right_times_dict)
    all_names_dict.update(left_times_dict) # do the left (after) last, so that we give precedence to those ones
    diff_times_dict = dict((name, from_seconds(to_seconds(left_times_dict.get(name,'0m0.0s')) - to_seconds(right_times_dict.get(name,'0m0.0s')), signed=True))
                           for name in all_names_dict.keys())
    # update to sort by approximate difference, first
    for name in all_names_dict.keys():
        all_names_dict[name] = (abs(int(to_seconds(diff_times_dict[name]))), to_seconds(all_names_dict[name]))

    names = sorted(all_names_dict.keys(), key=all_names_dict.get, reverse=descending)
    #names = get_sorted_file_list_from_times_dict(all_names_dict, descending=descending)
    # set the widths of each of the columns by the longest thing to go in that column
    left_sum = sum_times(left_times_dict.values())
    right_sum = sum_times(right_times_dict.values())
    diff_sum = from_seconds(sum(map(to_seconds, left_times_dict.values())) - sum(map(to_seconds, right_times_dict.values())), signed=True)
    left_width = max(max(map(len, left_times_dict.values())), len(left_sum))
    right_width = max(max(map(len, right_times_dict.values())), len(right_sum))
    far_right_width = max(max(map(len, diff_times_dict.values())), len(diff_sum))
    middle_width = max(map(len, names + ["File Name", "Total"]))
    format_string = "%%-%ds | %%-%ds | %%-%ds || %%-%ds" % (left_width, middle_width, right_width, far_right_width)
    header = format_string % (left_tag, "File Name", right_tag, "Change")
    total = format_string % (left_sum,
                             "Total",
                             right_sum,
                             diff_sum)
    # separator to go between headers and body
    sep = '-' * len(header)
    # the representation of the default value (0), to get replaced by N/A
    left_rep, right_rep, far_right_rep = ("%%-%ds" % left_width) % 0, ("%%-%ds" % right_width) % 0, ("%%-%ds" % far_right_width) % 0
    return '\n'.join([header, sep, total, sep] +
                     [format_string % (left_times_dict.get(name, 0),
                                       name,
                                       right_times_dict.get(name, 0),
                                       diff_times_dict.get(name, 0))
                      for name in names]).replace(left_rep, 'N/A'.center(len(left_rep))).replace(right_rep, 'N/A'.center(len(right_rep))).replace(far_right_rep, 'N/A'.center(len(far_right_rep)))

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print('Usage: %s LEFT_FILE_NAME RIGHT_FILE_NAME [OUTPUT_FILE_NAME]' % sys.argv[0])
        sys.exit(1)
    else:
        left_dict = get_times(sys.argv[1])
        right_dict = get_times(sys.argv[2])
        table = make_table_string(left_dict, right_dict)
        if len(sys.argv) == 3 or sys.argv[3] == '-':
            print(table)
        else:
            with open(sys.argv[3], 'w') as f:
                f.write(table)
