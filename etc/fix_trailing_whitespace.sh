#!/bin/bash

# This command removes trailing whitespace from all files in the repository.

git grep -l -z -E '\s+$' | xargs -0 sed -i 's/\s\+$//'
