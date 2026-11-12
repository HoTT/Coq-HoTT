#!/usr/bin/env bash

# Wrap the Rocq driver to report compiler concurrency on standard error.
# Use: make -jJ ROCQ=etc/coqccount.sh ...
# Counts may be smaller for very short jobs or jobs starting simultaneously.

ARGS=("$@")
CURFILE=
for arg in "$@"; do
    case "$arg" in
        --version|--print-version|-v|--help|-help|-h|-where|-config|-list-tags)
            exec rocq "$@" ;;
    esac
    [[ "$arg" == *.v ]] && CURFILE="$arg"
done

FIRST=0
while [[ "${ARGS[FIRST]-}" == -debug-shim ]]; do
    ((FIRST+=1))
done
case "${ARGS[FIRST]-}" in
    compile|c) ;;
    -*|*.v)
        [[ -n "$CURFILE" ]] || exec rocq "$@"
        ARGS=("${ARGS[@]:0:FIRST}" compile "${ARGS[@]:FIRST}")
        ;;
    *) exec rocq "$@" ;;
esac

# Do not count or annotate non-file calls.
[[ -n "$CURFILE" ]] || exec rocq "${ARGS[@]}"

# Select real workers first, then exclude check/repl workers by their arguments.
# Checking the process name also handles executable paths containing spaces.
count_compilers() {
    local pids
    pids=$(pgrep -x rocqworker) || true
    if [[ -z "$pids" ]]; then
        printf '0\n'
        return
    fi
    ps -ww -p "${pids//$'\n'/,}" -o command= 2>/dev/null |
        grep -Ec -- '(^|[[:space:]])--kind=compile([[:space:]]|$)' || true
}
rocq "${ARGS[@]}" &
PID=$!
sleep 0.001
CNT=$(count_compilers)
echo "-> $CNT $CURFILE" >&2

wait "$PID"
RET=$?
CNT=$(( $(count_compilers) + 1 ))
echo "<- $CNT $CURFILE" >&2
exit "$RET"
