"""Argument dispatch and timed compilation for the developer Rocq wrappers."""

import subprocess
import time


def prepare_command(args):
    """Accept Rocq driver calls, plus the legacy direct-file invocation."""
    args = list(args)
    queries = {'--version', '--print-version', '-v', '--help', '-help', '-h',
               '-where', '-config', '-list-tags'}
    # Queries can mention source files without compiling them.
    if any(arg in queries for arg in args):
        return ['rocq'] + args, []
    first = 0
    while first < len(args) and args[first] == '-debug-shim':
        first += 1
    tail = args[first:]
    files = [arg for arg in tail if arg.endswith('.v')]
    driver_compile = bool(tail) and tail[0] in ('compile', 'c')
    direct_compile = bool(files) and (tail[0].startswith('-') or tail[0].endswith('.v'))
    if not driver_compile and not direct_compile:
        return ['rocq'] + args, []
    if direct_compile:
        args.insert(first, 'compile')
    return ['rocq'] + args, files


def run_compiler(command, quiet=False, timeout=60):
    """Return (exit status, duration), using 1111 for a timeout."""
    start = time.perf_counter()
    output = subprocess.DEVNULL if quiet else None
    try:
        result = subprocess.run(command, timeout=timeout, stdout=output, stderr=output)
    except subprocess.TimeoutExpired:
        return 1111, time.perf_counter() - start
    elapsed = time.perf_counter() - start
    return (1111 if elapsed > timeout else result.returncode), elapsed
