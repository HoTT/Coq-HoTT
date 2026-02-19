#!/bin/bash

# Usage: find_slow_lines.sh [path]

find $1 -name '*.v.timing' -exec awk '{printf "%-55s %s\n", "{}:", $0}' {} \; \
  | sort -nr -k7 \
  | head -20 \
  | sed 's/.v.timing//' \
  | sed 's|\./||'
