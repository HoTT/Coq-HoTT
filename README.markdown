[![Build Status](https://api.travis-ci.org/HoTT/HoTT.png?branch=master)](https://travis-ci.org/HoTT/HoTT)

[Homotopy Type Theory](http://homotopytypetheory.org/) is an interpretation of
Martin-Löf’s intensional type theory into abstract homotopy theory. Propositional equality
is interpreted as homotopy and type isomorphism as homotopy equivalence. Logical
constructions in type theory then correspond to homotopy-invariant constructions on
spaces, while theorems and even proofs in the logical system inherit a homotopical
meaning. As the natural logic of homotopy, type theory is also related to higher category
theory as it is used e.g. in the notion of a higher topos.

The HoTT library is a development of homotopy-theoretic ideas in the Coq proof assistant.
It draws many ideas from Vladimir Voevodsky's
[Foundations](https://github.com/vladimirias/Foundations) library.

## INSTALLATION

Installation details are explained in the file `INSTALL.txt`. You will need to compile a
custom version of Coq which supports the `-indices-matter` flag, universe polymorphism, and
private types. We hope to have these pushed into standard Coq, but in the meanwhile the
Coq version is available at https://github.com/HoTT/coq/branches/trunk.  The particular
version of Coq which the current version of this repository is compatible is bundled as
a git submodule.

If you are looking for an older version of HoTT which works with standard Coq, have a look
at the one tagged as `pure-coq-8.3`. Note however that we do not support the old
library anymore.

## USAGE

It is possible to use the HoTT library directly on the command line with the `hoqtop`
script, but who does that?

It is probably better to use [Proof General](http://proofgeneral.inf.ed.ac.uk) and
[Emacs](http://www.gnu.org/software/emacs/). When Proof General asks you where to find the
`coqtop` executable, just point it to the `hoqtop` script. If Emacs runs a `coqtop`
without asking, you should probably customize set the variable `proof-prog-name-ask` to
`nil` (in Emacs type `C-h v proof-prog-name-ask RET` to see what this is about).

At the moment there is no `hoqide` equivalent of `coqide`, but getting one is high on our
to-do list.

## CONTRIBUTING

Contributions to the HoTT library are very welcome!  We use the “fork
and pull” model: to contribute, please [create your own
fork](https://help.github.com/articles/fork-a-repo) and [issue a pull
request](https://help.github.com/articles/using-pull-requests) when
you have code ready to join the main library.  When you make large
changes, feel free to include timing information in your commit
message; run `./etc/coq-scripts/timing/make-pretty-timed-diff.sh &&
git commit -at ./time-of-build-both.log`, or see the comments at the
top of `etc/coq-scripts/timing/make-pretty-timed-diff.sh` for more
detailed instructions and caveats.  To make use of these scripts, you
must first run `git submodule update --init --recursive`.  Note that
if you create a new file, you must update `Makefile_targets.mk`.  We
suggest running `make strict` rather than just `make`, so that you
will get an error if you forget.

## LICENSING

The library is released under the permissive BSD 2-clause license, see the file
`LICENSE.txt` for further information. In brief, this means you can do whatever you like
with it, as long as you preserve the Copyright messages. And of course, no warranty!
