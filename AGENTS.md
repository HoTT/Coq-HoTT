# AGENTS.md

Repository-wide guidance for coding agents. A more specific `AGENTS.md` in a
subdirectory takes precedence for files below it.

## Project

HoTT is a Rocq (formerly Coq) library for homotopy type theory. Library sources
live in `theories/`, additional developments in `contrib/`, tests in `test/`,
and developer tooling in `etc/`.

- Preserve the required `-noinit` and `-indices-matter` flags by using the
  project build rather than invoking Rocq with ad-hoc arguments.
- Note that `Basics` (especially `Basics.Overture`) provides many of the
  things usually provided by `Init` in standard Rocq developments.
- Look up the supported Rocq versions in the CI matrices
  (`.github/workflows/ci.yml`); avoid
  unnecessary version-specific features.

## Proof Development

- Read `doc/STYLE.md` before changing `.v` files and match the surrounding style.
  In particular, do not hard-wrap prose in Rocq comments.
- Prove results at their natural level of generality: consider arbitrary
  truncation levels, modalities, or reflective subuniverses when appropriate.
- Prefer reusable lemmas over long proofs, and keep intermediate goals readable
  enough for a human to follow.
- Useful project tactics include `napply`, `snapply`, `rapply`, `srapply`,
  `tapply`, `stapply`, and the `lhs`, `lhs_V`, `rhs`, and `rhs_V` tacticals
  (and primed variants) described in `doc/STYLE.md`.
- Preserve intended universe polymorphism while avoiding unnecessary universe
  parameters and constraints. Inspect universe-sensitive definitions with
  `About` or `Print` and `Set Printing Universes.`
- Add regression checks under `test/` when appropriate.
- Before stating a lemma, search `theories/` for an existing or more general
  form; if a close variant exists, generalize it in place rather than adding
  a new one.
- Do not add definitions that merely rename, specialize, or compose existing
  lemmas in one step; use the existing lemmas directly.
- Make arguments implicit when inferable from later arguments (objects from
  morphisms, groups from homomorphisms), and declare instances with
  `Instance` at the definition rather than wrapping them later.

## Working Rules

- Keep changes focused and avoid unrelated formatting or refactoring.
- Do not introduce `Admitted`, `admit`, or new axioms to finish a proof. Follow
  the axiom conventions in `doc/STYLE.md` when axioms are genuinely in scope.
- Do not edit generated files or build products such as `_CoqProject`,
  `Makefile.coq`, `*.vo`, or `_build/`.
- Require exactly what the file uses: no reliance on transitive imports, and
  no meta-file imports (`Categories`, `Basics`) from within their own
  subtrees.
- Add new library files to the closest meta-file above them in the folder
  structure, such as `theories/WildCat.v` or `theories/HoTT.v`.
- Do not stage, commit, or rewrite repository history unless explicitly asked.
- When asked to commit, keep commits atomic and self-contained, with tests
  and implementation grouped so that each commit is independently valid.

## Build and Test

Prefer Dune. Use `dune build` for fast feedback while iterating:

```sh
dune build
```

Before each commit, run the tests with `dune build test/` for fast feedback.
When the whole task is complete, run the full validation target `dune test`
(equivalent to `dune runtest`), which additionally runs `coqchk`:

```sh
dune test
```

Use `make -j2` only when a task specifically concerns the Make build or needs
to reproduce that CI path. Note that `make` will only build a file if `git add`
has been run on it, so you may stage files with `git add` for this purpose.
Finish with `git diff --check` and report what was and was not validated.

## Rocq MCP

When a Rocq MCP server is available, use it for quick proof inspection and
iteration. Treat it as optional fast feedback and validate final edits with the
normal Dune build and tests.
