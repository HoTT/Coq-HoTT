# HoTT Classes

Based on [Math Classes](https://math-classes.github.io/) but for [HoTT](https://github.com/hott/hott).

Notable differences:
- less stuff
- no setoids (HoTT has quotient types)

# Build

Dependencies:
- Coq with inductive-inductive types https://github.com/mattam82/coq/tree/IR
- HoTT branch https://github.com/SkySkimmer/HoTT/tree/with-IR must be present on your system, built with Coq with inductive-inductive types, with its `hoqc` and `hoqdep` in your `$PATH` or pointed to by `$HOQC` and `$HOQDEP` respectively.

Then run

    $ ./configure
    $ make

Use `./ide` to start hoqide with the right arguments, or look at its code to see what arguments are needed.

