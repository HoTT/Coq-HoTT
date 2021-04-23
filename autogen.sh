#!/usr/bin/env bash

# don't fall back on git if you interrupt or kill this script
trap "exit 1" SIGINT SIGTERM

echo "Warning: autogen.sh is not needed anymore" >&2

cat > configure <<EOF
#!/usr/bin/env bash
echo "Warning: autogen.sh is not needed anymore" >&2
EOF
chmod +x configure

if [ "$1" != "-skip-submodules" ] && command -v git >/dev/null 2>&1
then # git found
    if [ -d .git ] || [ -f .git ]
    then # we're in a git repository
	git submodule sync # update possibly changed urls
	git submodule update --init --recursive
    elif test ! -d etc/coq-scripts/timing
    then
	echo 'You are not in a git repo; the timing scripts at ./etc/coq-scripts/timing will not be available.'
    fi
elif test ! -d etc/coq-scripts/timing
then
    echo 'You do not have git; the timing scripts at ./etc/coq-scripts/timing will not be available.'
fi
