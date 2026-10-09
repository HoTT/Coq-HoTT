#!/usr/bin/env bash

# Wrap the Rocq driver to report compiler concurrency on standard error.
# Use: make -jJ ROCQ=etc/coqccount.sh ...
# Counts may be smaller for very short jobs or jobs starting simultaneously.

ARGS=("$@")
CURFILE=
for arg in "$@"; do
    [[ "$arg" == *.v ]] && CURFILE="$arg"
done

case "${1-}" in
    compile|c) ;;
    -*|*.v)
        [[ -n "$CURFILE" ]] || exec rocq "$@"
        ARGS=(compile "$@")
        ;;
    *) exec rocq "$@" ;;
esac

# Do not count or annotate version queries or other non-file calls.
[[ -n "$CURFILE" ]] || exec rocq "${ARGS[@]}"

# The driver execs rocqworker; only workers with --kind=compile count.
# Matching command lines excludes check/repl workers and this shell wrapper.
COMPILERS='^([^[:space:]]*/)?rocqworker --kind=compile([[:space:]]|$)'
rocq "${ARGS[@]}" &
PID=$!
sleep 0.001
CNT=$(pgrep -fc "$COMPILERS")
echo "-> $CNT $CURFILE" >&2

wait "$PID"
RET=$?
CNT=$(( $(pgrep -fc "$COMPILERS") + 1 ))
echo "<- $CNT $CURFILE" >&2
exit "$RET"
