# HoTT Classes

Based on [Math Classes](https://math-classes.github.io/) but for [HoTT](https://github.com/hott/hott).

Notable differences:
- less stuff
- no setoids (HoTT has quotient types)

# Build

Dependencies:
- HoTT must be present on your system, with `hoqc` and `hoqdep` in your `$PATH` or pointed to by `$HOQC` and `$HOQDEP` respectively.

If the set of `.v` files has changed since the last time,

    $ ./configure

Then

    $ make

