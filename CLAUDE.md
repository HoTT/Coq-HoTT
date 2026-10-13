@AGENTS.md

# Formalizing Booij's thesis (branch `abooij/claude-locators`)

The goal on this branch is to formalize Chapters 3–8 of A. B. Booij, *Analysis in Univalent Type Theory* (PhD thesis, Birmingham, 2020), `Booij2020PhD.pdf` in the repository root, next to `theories/Analysis/Locator.v`. `BLUEPRINT.md` lists every numbered result with its dependencies, target file, status and what Coq-HoTT already provides; keep it up to date as you work (status: `todo` → `stated` → `proved`).

The rules below come on top of `AGENTS.md` and `doc/STYLE.md`.

## Structure versus property

- Use Σ-types (`{x : A & P x}`, records) for structure: data you compute with, such as a locator, a bound `{q : Q & ' q < x}`, a modulus, a limit operator or a chosen witness.
- Use the truncated `∃` (`hexists`, `merely`, `hor`, i.e. `Tr (-1)`) for properties. Where the thesis writes `∃` or `∨`, the formal statement uses `hexists`/`hor`; where it writes `Σ` or `+`, it uses `sig`/`sum`.
- Never weaken a structure to a property or strengthen a property to a structure silently. When the thesis turns property into structure (bounded search, Lemma 6.7.3, Theorem 6.10.3), make that the content of an explicit lemma.

## Naming and `Thesis.v`

- Give results ordinary descriptive names in the style of the surrounding code (see `doc/STYLE.md`); do not encode thesis numbers in names. Reuse existing Coq-HoTT names rather than adding aliases (see `AGENTS.md`).
- Register every numbered item of the thesis that has been formalized in `theories/Analysis/Thesis.v`, under a comment with its thesis number and statement in words, as a `Check` of the result(s) that formalize it, e.g. `(** Lemma 6.6.1. A real with a locator has rational bounds. *)` followed by `Check lower_bound.` and `Check upper_bound.` Keep the file in thesis order, and add an entry only once the item is proved.
- In the result's own file, a short comment citing the thesis number (e.g. `(** Lemma 6.6.1 of Booij's thesis. *)`) is welcome but optional.

## Search first

- Before assuming a lemma exists, and before stating a new one, search for it: `Search`, `SearchPattern`, `Locate` and `About` (through the Rocq MCP server if available, or in a scratch file built with `bin/build`), and `grep` over `theories/`.
- Never cite a lemma name from memory or from `BLUEPRINT.md` without checking that it exists with the expected statement; the blueprint records what existed when it was written.

## Axioms and stubs

- Do not add new axioms: no `Axiom`, `Parameter`, `Conjecture` or top-level `Hypothesis`/`Variable`. Assumptions such as `Funext`, `Univalence`, `PropResizing` or `ExcludedMiddle` enter only as typeclass arguments or `Context`, following `doc/STYLE.md`.
- `Admitted`, `admit` and `give_up` are allowed only in files marked as stubs: a file is a stub when one of its first ten lines is exactly `(* STUB *)`. A hook in `.claude/settings.json` blocks other edits that add them. Stub files must not be added to `theories/HoTT.v` or other meta-files; remove the marker once the file is complete.

## Building

- `bin/build` builds the library with Rocq 9.1 inside the `rocq/rocq-prover:9.1` Docker image (`dune build`); `bin/build FILE.v` builds one file and its dependencies; `bin/build test` builds `test/`; `bin/build check` runs `dune test` (including `rocqchk`). It needs a running Docker daemon; a SessionStart hook starts one, and otherwise run `dockerd &`.
- A hook in `.claude/settings.json` runs `bin/build` on every edited `.v` file and reports errors back. Fix them before moving on.
- A clean build of the library takes about 1.5 minutes on 4 cores; `bin/build check` takes about 30 seconds more.
