"""Argument dispatch and timed compilation for the developer Rocq wrappers."""

import subprocess
import time


def prepare_command(args):
    """Accept Rocq driver calls, plus the legacy direct-file invocation."""
    args = list(args)
    files = [arg for arg in args if arg.endswith('.v')]
    driver_compile = bool(args) and args[0] in ('compile', 'c')
    direct_compile = bool(files) and (args[0].startswith('-') or args[0].endswith('.v'))
    if not driver_compile and not direct_compile:
        return ['rocq'] + args, []
    if direct_compile:
        args.insert(0, 'compile')
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
