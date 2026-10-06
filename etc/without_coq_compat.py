#!/usr/bin/env python3
"""Run a command with legacy Coq executables removed from PATH."""
import contextlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

# Do not exclude genuine third-party tools such as coq-lsp.
COMPAT = frozenset({
    "coq", "coqc", "coqc.byte", "coqtop", "coqtop.byte", "coqchk",
    "coqdep", "coqdoc", "coq_makefile", "coqworker", "coqidetop",
    "coqidetop.byte", "coqpp", "coqnative", "coqwc",
})


@contextlib.contextmanager
def native_environment(env):
    """Keep PATH precedence, arguments, and non-PATH toolchain settings."""
    with tempfile.TemporaryDirectory(prefix="hott-native-rocq-") as directory:
        paths = []
        for index, entry in enumerate(env.get("PATH", "").split(os.pathsep)):
            source = Path(entry or ".").resolve()
            if not source.is_dir():
                continue
            programs = list(source.iterdir())
            if not any(program.name in COMPAT for program in programs):
                # Keep native tool locations stable for Dune caching.
                paths.append(str(source))
                continue
            target = Path(directory) / str(index)
            target.mkdir()
            for program in programs:
                if (program.name not in COMPAT and program.is_file()
                        and os.access(program, os.X_OK)):
                    (target / program.name).symlink_to(program)
            paths.append(str(target))
        result = dict(env)
        result["PATH"] = os.pathsep.join(paths)
        # COQBIN can bypass PATH in generated Make rules.
        result.pop("COQBIN", None)
        yield result


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if not argv:
        print("usage: without_coq_compat.py COMMAND [ARG ...]", file=sys.stderr)
        return 2
    with native_environment(os.environ) as env:
        try:
            status = subprocess.call(argv, env=env)
        except FileNotFoundError as error:
            print(str(error), file=sys.stderr)
            return 127
        return status if status >= 0 else 128 - status


if __name__ == "__main__":
    sys.exit(main())
