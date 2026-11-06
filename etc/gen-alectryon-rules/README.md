# Alectryon Rules Generator

This tool generates Dune rules for parallel Alectryon documentation of the Rocq sources.

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

Alectryon would otherwise request each goal separately from coq-lsp. Instead,
`fcc` dumps all goals in one batch, and the converter makes that output
available to Alectryon. `fcc`, `coq-lsp.plugin.goaldump`, and the `coq.io.json`
frontend are names supplied by those tools; they are not renamed to `rocq`.

## Generated Files

For each `.v` file, the rule produces:
- `<name>.html` - The Alectryon HTML documentation
- `<name>.v.fcc.log` - Log output from fcc (useful for debugging)

Files are output to `alectryon-html/` with flattened names (e.g.,
`theories/WildCat/Core.v` becomes `HoTT.WildCat.Core.html`).

## Usage

```bash
# Initialize the documentation submodules once
git submodule update --init etc/alectryon etc/coq-scripts

# Build all documentation (fcc/goaldump must match the Rocq version)
dune build @alectryon

# Build documentation for a single file
dune build alectryon-html/HoTT.WildCat.Core.html
```

## Dependencies

- `fcc` from coq-lsp with the goaldump plugin (`coq-lsp.plugin.goaldump`)
- Python 3 with Alectryon's dependencies and the initialized `etc/alectryon/` submodule
- `goaldump-to-alectryon.py` converter script (in this directory)

## How It Works

The rules are generated dynamically using dune's `dynamic_include` feature:

1. `gen_alectryon_rules.exe` scans `theories/` and `contrib/` for `.v` files
2. It outputs dune rules in S-expression format to `alectryon_rules.sexp`
3. The main `dune` file includes these rules via `(dynamic_include
   ../alectryon_rules.sexp)` in the `alectryon-html` subdirectory

Each rule uses `(sandbox always)` to ensure parallel builds don't interfere
with each other, since `fcc` writes intermediate files next to the source.
