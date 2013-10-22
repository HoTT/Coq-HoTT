#!/usr/bin/python
from __future__ import with_statement
import os, sys, re
from TimeFileMaker import *

def make_table_string(left_times_dict, right_times_dict,
                      descending=True,
                      left_tag="After", right_tag="Before"):
    all_names_dict = dict()
    all_names_dict.update(right_times_dict)
    all_names_dict.update(left_times_dict) # do the left (after) last, so that we give precedence to those ones
    names = get_sorted_file_list_from_times_dict(all_names_dict, descending=descending)
    left_width = max(max(map(len, left_times_dict.values())), len(sum_times(left_times_dict.values())))
    right_width = max(max(map(len, right_times_dict.values())), len(sum_times(right_times_dict.values())))
    middle_width = max(map(len, names + ["File Name", "Total"]))
    format_string = "%%-%ds | %%-%ds | %%-%ds" % (left_width, middle_width, right_width)
    header = format_string % (left_tag, "File Name", right_tag)
    total = format_string % (sum_times(left_times_dict.values()),
                             "Total",
                             sum_times(right_times_dict.values()))
    sep = '-' * len(header)
    left_rep, right_rep = ("%%-%ds" % left_width) % 0, ("%%-%ds" % right_width) % 0
    return '\n'.join([header, sep, total, sep] +
                     [format_string % (left_times_dict.get(name, 0),
                                       name,
                                       right_times_dict.get(name, 0))
                      for name in names]).replace(left_rep, 'N/A'.center(len(left_rep))).replace(right_rep, 'N/A'.center(len(right_rep)))

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
