# Alectryon Rules Generator

This tool generates dune rules for parallel Alectryon documentation processing.

## Overview

The generator creates one dune rule per `.v` file in `theories/` and
`contrib/`. Each rule:

1. Runs `fcc` (Flèche Coq Compiler from coq-lsp) with the goaldump plugin to
   extract proof goals
2. Converts the goaldump JSON to Alectryon's JSON format using
   `goaldump-to-alectryon.py` (in this directory)
3. Runs Alectryon with the `coq.io.json` frontend to produce HTML

## Why fcc instead of coq-lsp?

Alectryon normally uses coq-lsp to extract proof states, but this is slow
because coq-lsp is designed for interactive editing with incremental
compilation. For batch documentation generation, `fcc` is much faster as it's
optimized for single-pass compilation.

alectryon will normally ask coq-lsp for each goal separately which takes way
too long. By getting fcc (the Coq compiler based on internals of coq-lsp) to
dump all the goals, we can process them as something alectryon can understand.

## Generated Files

For each `.v` file, the rule produces:
- `<name>.html` - The Alectryon HTML documentation
- `<name>.v.fcc.log` - Log output from fcc (useful for debugging)

Files are output to `alectryon-html/` with flattened names (e.g.,
`theories/WildCat/Core.v` becomes `theories.WildCat.Core.html`).

## Usage

```bash
# Build all documentation
dune build @alectryon

# Build documentation for a single file
dune build alectryon-html/theories.WildCat.Core.html
```

## Dependencies

- `fcc` from coq-lsp with the goaldump plugin (`coq-lsp.plugin.goaldump`)
- Python 3 with the Alectryon package (via `etc/alectryon/`)
- `goaldump-to-alectryon.py` converter script (in this directory)

## How It Works

The rules are generated dynamically using dune's `dynamic_include` feature:

1. `gen_alectryon_rules.exe` scans `theories/` and `contrib/` for `.v` files
2. It outputs dune rules in S-expression format to `alectryon_rules.sexp`
3. The main `dune` file includes these rules via `(dynamic_include
   ../alectryon_rules.sexp)` in the `alectryon-html` subdirectory

Each rule uses `(sandbox always)` to ensure parallel builds don't interfere
with each other, since `fcc` writes intermediate files next to the source.

## fcc Exit Codes

Note: `fcc` may return exit code 1 even on successful compilation (due to "file
not in workspace" warnings). The rules use `(with-accepted-exit-codes (or 0 1)
...)` to handle this.
