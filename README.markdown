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

## INSTALATION

Installation details are explained in the file `INSTALL.txt`. You will need to compile a
custom version of Coq which supports the `-relevant-equality` and
`-warn-universe-inconsistency` command-line options. We hope to have these options pushed
into standard Coq.

If you are looking for an older version of HoTT which works with standard Coq, have a look
at the one tagged as `pure-coq-8.3`. Note however that we do not support the old
library anymore.

## USAGE

It is possible to use the HoTT library directly on the command line with the `hoqtop`
script, but who does that?

It is probably better o use [Proof General](http://proofgeneral.inf.ed.ac.uk) and
[Emacs](http://www.gnu.org/software/emacs/). When Proof General asks you where to find the
`coqtop` executable, just point it to the `hoqtop` script. If Emacs runs a `coqtop`
without asking, you should probably customize set the variable `proof-prog-name-ask` to
`nil` (in Emacs type `C-h v proof-prog-name-ask RET` to see what this is about).

At the moment there is no `hoqide` equivalent of `coqide`, but getting one is high on our
to-do list.

## LICENSING

The library is released under the permissive BSD 2-clause license, see the file
`LICENSE.txt` for further information. In brief, this means you can do whatever you like
with it, as long as you preserve the Copyright messages. And of course, no warranty!
