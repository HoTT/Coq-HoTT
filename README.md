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
[Foundations](https://github.com/vladimirias/Foundations) library (which has since been
incorporated into the [UniMath](https://github.com/UniMath/UniMath) library) and also
cross-pollinates with the [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) library.
Recently, there are also the [Lean](https://github.com/leanprover/lean/blob/master/hott/hott.md) library and the [cubical](https://github.com/mortberg/cubicaltt) type checker.

More information about this libary can be found in:
* _The HoTT Library: A formalization of homotopy type theory in Coq_, 
Andrej Bauer, Jason Gross, Peter LeFanu Lumsdaine, Mike Shulman, Matthieu Sozeau, Bas Spitters, 2016 [arxiv](https://arxiv.org/abs/1610.04591) [CPP17](http://cpp2017.mpi-sws.org/)

## INSTALLATION

Installation details are explained in the file `INSTALL.md`. 

## USAGE

It is possible to use the HoTT library directly on the command line with the `hoqtop`
script, but who does that?

It is probably better to use [Proof General](http://proofgeneral.inf.ed.ac.uk) and
[Emacs](http://www.gnu.org/software/emacs/). When Proof General asks you where to find the
`coqtop` executable, just point it to the `hoqtop` script. If Emacs runs a `coqtop`
without asking, you should probably customize set the variable `proof-prog-name-ask` to
`nil` (in Emacs type `C-h v proof-prog-name-ask RET` to see what this is about).

There is also a script called `hoqide` that runs Coq's built-in GUI `coqide`
with `hoqtop` as the underlying `coqtop`.

## CONTRIBUTING

Contributions to the HoTT library are very welcome!  For style
guidelines and further information, see the file `STYLE.md`.

## LICENSING

The library is released under the permissive BSD 2-clause license, see the file
`LICENSE.txt` for further information. In brief, this means you can do whatever you like
with it, as long as you preserve the Copyright messages. And of course, no warranty!

## Wiki

More information can be found in the [Wiki](https://github.com/HoTT/HoTT/wiki).
