# HoTT Classes

Based on [Math Classes](https://math-classes.github.io/) but for [HoTT](https://github.com/hott/hott).

Notable differences:
- less stuff
- no setoids (HoTT has quotient types)

# Publications

See SCIENCE.md

# Build

You can follow what travis does ([.travis.yml](.travis.yml), [build-dependencies.sh](build-dependencies.sh) and [build-HoTTClasses.sh](build-HoTTClasses.sh)), or:

- Install dependencies:

    - [Coq with inductive-inductive types](https://github.com/mattam82/coq/tree/IR) including its depencies (some Ocaml libraries)
    - [HoTT modified to compile with Coq trunk](https://github.com/SkySkimmer/HoTT/tree/mz-8.7)

- In this guide they are installed respectively in directories `coq/` and `HoTT/`.

- `./configure --hoqdir HoTT/ --coqbin coq/bin/`

- `make`

# Build with unmodified dependencies

It is possible to build some of HoTTClasses with Coq 8.6 and HoTT
master. Only the files in [theories/IR](theories/IR) and the summaries
at the root of [theories](theories) will be skipped.

You will need to pass an additional `--no-ir` to HoTTClasses's configure script.

# Using IDEs

## Coqide

The `./ide` script only works if HoTT/ is in your `$PATH`, use `/path/to/HoTT/hoqide -R theories HoTTClasses` otherwise.

## Proof General

[Proof General](https://github.com/ProofGeneral/PG/) understands the `_CoqProject` produced by `./configure`. `./configure` also sets up `.dir-locals.el` so that PG calls the right hoqtop program.
