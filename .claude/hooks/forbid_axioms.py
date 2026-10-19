#!/usr/bin/env python3
"""PreToolUse hook: block edits to .v files that add Axiom, Admitted or admit,
or that add references to Booij's thesis outside contrib/Booij2020Thesis.v.

Files marked as stubs are exempt. A file is a stub when one of its first ten
lines is exactly the comment

    (* STUB *)

For an existing file the marker must already be on disk, so an edit cannot
exempt itself by adding the marker; a new file created with Write may carry
the marker in its content.

The check counts occurrences outside comments and strings, so an edit that
merely moves or keeps existing admits is allowed. Parameter and Conjecture are
treated like Axiom, since they declare axioms too, and give_up like admit.

Thesis references ("Lemma 6.7.1", "Booij", "thesis", ...) belong only in
Booij2020Thesis.v and BLUEPRINT.md (see CLAUDE.md); this applies to stubs too. Lines
mentioning the HoTT book are exempt, since its numbering looks the same.
"""

import json
import os
import re
import sys

STUB_MARKER = "(* STUB *)"

FORBIDDEN = re.compile(
    r"(?<![\w'.])"
    r"(Axioms?|Parameters?|Conjectures?|Admitted|admit|give_up)"
    r"(?![\w']|\.\w)"
)


THESIS_REF = re.compile(
    r"\b(?:Lemma|Theorem|Thm|Definition|Def|Corollary|Cor|Proposition|Prop|Remark|Rem"
    r"|Example|Ex|Conjecture|Conj|Section|Discussion)\.?\s+[3-8](?:\.[0-9]+){1,2}\b"
    r"|\bBooij\b|\b[Tt]hesis\b"
)


def thesis_refs(text):
    return [
        m.group(0)
        for line in (text or "").splitlines()
        if "book" not in line.lower()
        for m in THESIS_REF.finditer(line)
    ]


def added_thesis_refs(pairs):
    added = []
    for old, new in pairs:
        before, after = thesis_refs(old), thesis_refs(new)
        added += [w for w in dict.fromkeys(after) if after.count(w) > before.count(w)]
    return added


def strip_comments_and_strings(text):
    """Remove (nested) Rocq comments and string literals."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            out.append(" ")
        elif depth:
            i += 1
        elif text[i] == '"':
            # Rocq strings escape a quote by doubling it.
            i += 1
            while i < n:
                if text[i] == '"':
                    if text.startswith('""', i):
                        i += 2
                        continue
                    i += 1
                    break
                i += 1
            out.append(' "" ')
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def count_forbidden(text):
    return [m.group(1) for m in FORBIDDEN.finditer(strip_comments_and_strings(text or ""))]


def is_stub(text):
    return any(line.strip() == STUB_MARKER for line in (text or "").splitlines()[:10])


def main():
    payload = json.load(sys.stdin)
    tool = payload.get("tool_name", "")
    inp = payload.get("tool_input", {}) or {}
    path = inp.get("file_path") or ""
    if not path.endswith(".v"):
        return 0

    try:
        with open(path, encoding="utf-8") as f:
            current = f.read()
        exists = True
    except OSError:
        current = ""
        exists = False

    if tool == "Write":
        pairs = [(current, inp.get("content", ""))]
        stub = is_stub(current) if exists else is_stub(inp.get("content", ""))
    elif tool == "Edit":
        pairs = [(inp.get("old_string", ""), inp.get("new_string", ""))]
        stub = is_stub(current)
    elif tool == "MultiEdit":
        pairs = [(e.get("old_string", ""), e.get("new_string", "")) for e in inp.get("edits", [])]
        stub = is_stub(current)
    else:
        return 0

    refs = [] if os.path.basename(path) == "Booij2020Thesis.v" else added_thesis_refs(pairs)
    if refs:
        deny(
            f"Blocked: this edit adds thesis references ({', '.join(refs)}) to {os.path.relpath(path)}. "
            "Thesis numbers belong only in contrib/Booij2020Thesis.v and BLUEPRINT.md (see CLAUDE.md); "
            "describe the mathematics instead, and register the result in contrib/Booij2020Thesis.v once it is proved."
        )
        return 0

    if stub:
        return 0

    added = []
    for old, new in pairs:
        before, after = count_forbidden(old), count_forbidden(new)
        for word in set(after):
            extra = after.count(word) - before.count(word)
            if extra > 0:
                added.extend([word] * extra)

    if not added:
        return 0

    words = ", ".join(sorted(set(added)))
    reason = (
        f"Blocked: this edit adds {words} to {os.path.relpath(path)}, which is not marked as a stub. "
        "Do not introduce axioms or admitted proofs (see CLAUDE.md). Finish the proof, or, if this "
        f"file is a deliberate blueprint stub, one of its first ten lines must already be {STUB_MARKER}."
    )
    deny(reason)
    return 0


def deny(reason):
    json.dump(
        {
            "hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "deny",
                "permissionDecisionReason": reason,
            }
        },
        sys.stdout,
    )


if __name__ == "__main__":
    sys.exit(main())
