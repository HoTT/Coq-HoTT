@AGENTS.md

# Formalizing Booij's thesis (branch `abooij/claude-locators`)

The goal on this branch is to formalize Chapters 3–8 of A. B. Booij, *Analysis in Univalent Type Theory* (PhD thesis, Birmingham, 2020), `Booij2020PhD.pdf` in the repository root, next to `theories/Analysis/Locator.v`. `BLUEPRINT.md` lists every numbered result with its dependencies, target file, status and what Coq-HoTT already provides; keep it up to date as you work (status: `todo` → `stated` → `proved`). Page numbers in this file and in task briefs are the thesis's own printed page numbers; the PDF's page numbers are 11 higher (thesis page 130 is PDF page 141).

The rules below come on top of `AGENTS.md` and `doc/STYLE.md`.

## Structure versus property

- Use Σ-types (`{x : A & P x}`, records) for structure: data you compute with, such as a locator, a bound `{q : Q & ' q < x}`, a modulus, a limit operator or a chosen witness.
- Use the truncated `∃` (`hexists`, `merely`, `hor`, i.e. `Tr (-1)`) for properties. Where the thesis writes `∃` or `∨`, the formal statement uses `hexists`/`hor`; where it writes `Σ` or `+`, it uses `sig`/`sum`.
- Never weaken a structure to a property or strengthen a property to a structure silently. When the thesis turns property into structure (bounded search, Lemma 6.7.3, Theorem 6.10.3), make that the content of an explicit lemma.

## Naming and `Booij2020Thesis.v`

- Give results ordinary descriptive names in the style of the surrounding code (see `doc/STYLE.md`); do not encode thesis numbers in names. Reuse existing Coq-HoTT names rather than adding aliases (see `AGENTS.md`).
- Register every numbered item of the thesis that has been formalized in `contrib/Booij2020Thesis.v`, the index in the style of `contrib/HoTTBook.v`: an entry with a marker line and a heading such as `(** Lemma 6.6.1 *)`, defining aliases `Definition Booij2020Thesis_6_6_1_item_i := @lower_bound.` and `Definition Booij2020Thesis_6_6_1_item_ii := @upper_bound.` for the result(s) that formalize it (see the notes at the top of that file). Keep the file in thesis order, and add an entry only once the item is proved.
- Thesis numbers appear only in `contrib/Booij2020Thesis.v` and `BLUEPRINT.md`. The hook also rejects the words "thesis" and "Booij" in `.v` files outside `Booij2020Thesis.v`; refer to the mathematics or to published sources (e.g. "HoTT book, Theorem 11.3.50") instead. Do not mention them anywhere else: not in names, doc comments, proof comments or TODOs in `.v` files; hooks block edits and commits that add them. Describe the mathematics instead (e.g. "TODO: prove that the inclusion of [Q] preserves the order", not "TODO: Lemma 4.3.3").

## Search first

- Before assuming a lemma exists, and before stating a new one, search for it: `Search`, `SearchPattern`, `Locate` and `About` (through the Rocq MCP server if available, or in a scratch file checked with `bin/build scratch FILE.v`), and `grep` over `theories/`.
- Never cite a lemma name from memory or from `BLUEPRINT.md` without checking that it exists with the expected statement; the blueprint records what existed when it was written.

## Axioms and stubs

- Do not add new axioms: no `Axiom`, `Parameter`, `Conjecture` or top-level `Hypothesis`/`Variable`. Assumptions such as `Funext`, `Univalence`, `PropResizing` or `ExcludedMiddle` enter only as typeclass arguments or `Context`, following `doc/STYLE.md`.
- `Admitted`, `admit` and `give_up` are allowed only in files marked as stubs: a file is a stub when one of its first ten lines is exactly `(* STUB *)`. Hooks in `.claude/settings.json` block other edits that add them, and block commits that add them. Stub files must not be added to `theories/HoTT.v` or other meta-files; remove the marker once the file is complete.

## Building

- `bin/build` builds the library with Rocq 9.1 inside the `rocq/rocq-prover:9.1` Docker image (`dune build`); `bin/build FILE.v` builds one file and its dependencies; `bin/build test` builds `test/`; `bin/build check` runs `dune test` (including `rocqchk`). It needs a running Docker daemon, which it starts itself when it can; otherwise run `dockerd &`.
- `bin/build scratch FILE.v` builds the library and then compiles `FILE.v`, which may live anywhere (e.g. your scratchpad), against it, printing its output. Use it for `Search`, `Check` and drafting proofs; it takes under a second once the library is built. Since it builds the whole library first, a half-written file in `theories/` blocks it: draft new material in the scratchpad and move it into `theories/` once it compiles.
- CI also builds with Rocq 9.2 and the development version. To check a change against them, run `bin/build` with `ROCQ_IMAGE=rocq/rocq-prover:9.2` or `ROCQ_IMAGE=rocq/rocq-prover:dev`, preferably in a separate `git worktree` so that the 9.1 build in `_build/` is not invalidated. Known differences: `is` is a keyword on dev, so do not use it as a name; on 9.2, definitions inside a section cannot add universe constraints on the section's universes (e.g. by applying a general result to the Dedekind reals), so state such definitions outside a section.
- To wait for a build, run it in the foreground or in the background with a notification; do not poll with `pgrep -f` or kill with `pkill -f` on a pattern such as `bin/build`, which also matches the polling command itself (and killed the calling shell in one track).
- A hook in `.claude/settings.json` runs `bin/build` on every `.v` file edited with the Edit or Write tools and reports errors back; fix them before moving on. Files changed from the shell are not checked until you commit: another hook typechecks every changed `.v` file, and checks it for axioms and admits, before each `git commit`, and blocks the commit if anything fails.

## Working on a track

- Re-read this file before each commit: the rules may have changed since you started, and changes are announced only by updating it.
- Edit only your own rows of `BLUEPRINT.md`.
- A clean build of the library takes about 1.5 minutes on 4 cores; `bin/build check` takes about 30 seconds more.

## Proof tips

- Do not use the `ring` tactics from `Classes/tactics/` (`ring_with_nat`, `ring_with_integers`): they need extra assumptions such as `Univalence` and can run for minutes even on small identities. Prove ring identities by hand with rewriting lemmas.
- Universe levels: constants such as `Le` and `relation_pointwise` are not cumulative, so an instance stated at other levels is silently not found. Inspect levels with `Set Printing Universes` and `About`, and state levels explicitly where instances must match. Rocq cannot use `max(u, v)` as a universe instance, so a statement about several universes may need one extra universe above them all; that is fine. Avoid unnecessary universe parameters on main definitions, but an extra parameter that would take many `@{...}` annotations to remove is acceptable; readability wins.
- Concrete models (`NatPair.Z`, the fractions in `Classes/implementations/integer_fractions.v`, the Dedekind reals) have pinned universes, because some upstream sections tie the universe of a target to that of a source (see "Known problems" in `BLUEPRINT.md`). Applying a general result to them can fail on a universe constraint, or take minutes to elaborate; do not build new results on the concrete models unless the task asks for it.
- `archimedean_dedekindreals` carries a different characteristic-0 proof than `orderedfield_dedekindreals`, so instance search for field results applied to the Dedekind reals fails with an error listing every argument; use `archimedean_property_change_char` (in `Analysis/RealsInclusions.v`) to transport the Archimedean property.
- Definitions that quantify over `Qpos Q` should take `{Qlt : Lt@{UQ UQ} Q}` (as `Classes/theory/rationals.v` does); otherwise instantiating them with a closeness relation can leave an unsolvable `Lt` evar.
- A scratch file must `Require Import` every module whose `#[export]` instances and hints it relies on; a missing import looks like a missing instance.
- `rewrite ... at n` fails with "Setoid library not loaded"; use `lhs`/`rhs`, `ap`, or a local `assert` instead.
- Inside `mc_scope`, `*` is multiplication even in a type; write `(A * B)%type` for a product type, for example inside a Σ-type. When the product mixes with arithmetic, as in `(0 < d) * (d * z < e)`, `%type` would turn the inner `*` into a product too; write `prod (0 < d) (d * z < e)` instead.
- Typeclass search does not turn a goal `0 < ' (' e)` into a `PropHolds` instance; apply the positivity lemma directly. A result type `{d : Qpos Q & ...}` inside a section with many `Q` instances can leave `Qpos` evars; returning `{d : Q & 0 < d * ...}` and building the `Qpos` at the use site works.
- Before writing a helper lemma, grep `theories/Analysis/` and `Classes/orders/`: most duplicates removed in the style pass were short arguments that several files had re-proved.
- Keep proofs short and readable: split a long proof into lemmas that each state one step of the argument. For a long pair of symmetric statements (lower and upper bounds, left and right), look for the lemmas the two proofs share; derive one statement from the other (by negation or the order dual) only where that is the neatest solution.
- Prefer `napply f` (or `rapply f` when typeclass arguments remain, `tapply` as a last resort) over `refine (f _ _ _)`, `apply (f _ _)` or `exact (f _ _)`; it fills in the trailing arguments itself. To reason step by step on one side of an equation use `lhs`, `rhs`, `lhs_V` and `rhs_V`, and for any transitive relation such as `≤`, `<` or closeness the primed versions (`lhs' exact h` for `refine (transitivity h _)`, `rhs_V' exact h` for `refine (transitivity _ h)`; `rhs'` needs symmetry). See `doc/STYLE.md`.
