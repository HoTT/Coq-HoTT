#!/bin/bash

# This command fixes the end-of-file newlines for all files in the repository.

while IFS= read -r file; do
  # Check if the file is a regular file
  if [ -f "$file" ]; then
    if [ -n "$(tail -c 1 "$file")" ]; then
      echo "Adding newline to file: $file"
      echo >> "$file"
      git add "$file"
    fi
  fi
done < <(git ls-files)
