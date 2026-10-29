#!/usr/bin/env python3
"""PreToolUse hook on Bash: before a `git commit`, check the .v files it commits.

The edit hooks only see edits made with the Edit/Write tools, not files changed
from the shell. This hook closes the gap at commit time: for every .v file that
differs from HEAD (staged or not), it applies the same rule as forbid_axioms.py
(no added Axiom/Parameter/Conjecture/Admitted/admit/give_up outside stubs) and
typechecks the file with bin/build. It also rejects added thesis references
outside Booij2020Thesis.v, as forbid_axioms.py does, and added applications padded with
underscores such as `refine (f _ _ _ h)`, which should use the napply family (see
CLAUDE.md, "Proof tips"). Any failure blocks the commit (exit 2) and
the reason is fed back to Claude.
"""

import importlib.util
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("forbid_axioms", os.path.join(HERE, "forbid_axioms.py"))
forbid = importlib.util.module_from_spec(spec)
spec.loader.exec_module(forbid)


# `refine (f _ _ ...)`, `apply (f _ _)`, `exact (@f _ _ ...)`: two or more underscores right after the head.
PADDED = re.compile(r"\b(?:refine|apply|exact|eapply|simple refine)\s*\(\s*@?[\w.']+(?:\s+_){2,}(?![\w'])")


def padded_count(text):
    return len(PADDED.findall(text))


def git(*args, check=True):
    return subprocess.run(["git", *args], capture_output=True, text=True, check=check).stdout


def main():
    payload = json.load(sys.stdin)
    command = (payload.get("tool_input") or {}).get("command", "")
    if not re.search(r"\bgit\b[^;&|]*\bcommit\b", command):
        return 0

    root = git("rev-parse", "--show-toplevel").strip()
    os.chdir(root)
    files = [f for f in git("diff", "HEAD", "--name-only", "--diff-filter=AM", "--", "*.v").split() if os.path.isfile(f)]
    if not files:
        return 0

    problems = []
    for f in files:
        old = subprocess.run(["git", "show", f"HEAD:{f}"], capture_output=True, text=True).stdout
        new = open(f, encoding="utf-8").read()
        if os.path.basename(f) != "Booij2020Thesis.v":
            refs = forbid.added_thesis_refs([(old, new)])
            if refs:
                problems.append(f"{f} adds thesis references ({', '.join(refs)}); they belong only in Booij2020Thesis.v.")
        if padded_count(new) > padded_count(old):
            problems.append(f"{f} adds applications padded with underscores (e.g. `refine (f _ _ _ h)`); use napply, rapply or tapply instead, or lhs'/rhs_V' for transitivity steps (see CLAUDE.md, \"Proof tips\").")
        # As in forbid_axioms.py, an existing file must already have been a stub.
        stub = forbid.is_stub(old) if old else forbid.is_stub(new)
        if stub:
            continue
        before, after = forbid.count_forbidden(old), forbid.count_forbidden(new)
        added = sorted({w for w in after if after.count(w) > before.count(w)})
        if added:
            problems.append(f"{f} adds {', '.join(added)} but is not marked {forbid.STUB_MARKER}.")

    build = subprocess.run([os.path.join(root, "bin", "build"), *files], capture_output=True, text=True)
    if build.returncode != 0:
        out = re.sub(r"\x1b\[[0-9;]*m", "", build.stdout + build.stderr)
        problems.append("bin/build failed on the files being committed:\n" + "\n".join(out.splitlines()[-80:]))

    if problems:
        print("Commit blocked by .claude/hooks/commit_guard.py:\n" + "\n".join(problems), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
