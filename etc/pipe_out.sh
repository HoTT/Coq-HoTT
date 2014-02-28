#!/usr/bin/env bash
file="$1"
shift
"$@" > "$file"
