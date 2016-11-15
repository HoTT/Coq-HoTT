# HoTT Classes

Based on [Math Classes](https://math-classes.github.io/) but for [HoTT](https://github.com/hott/hott).

Notable differences:
- less stuff
- no setoids (HoTT has quotient types)

# Build

Dependencies:
- Dependencies of Coq trunk. Coq's `configure` should warn you if some are missing.
- Coq with inductive-inductive types https://github.com/mattam82/coq/tree/IR
- HoTT branch https://github.com/SkySkimmer/HoTT/tree/with-IR must be present on your system, built with Coq with inductive-inductive types, with its `hoqc` and `hoqdep` in your `$PATH` or pointed to by `$HOQC` and `$HOQDEP` respectively.

Then run

    $ ./configure
    $ make

Use `./ide` to start hoqide with the right arguments, or look at its code to see what arguments are needed.


# Install from archives
Run the build-HoTTClasses.sh script with `bash` in some directory. It will use `sudo apt-get` to install dependencies of Coq and autoconf for HoTT, download archives for Coq, HoTT and HoTTClasses and build everything.
You can also read it to see what needs to be done.
