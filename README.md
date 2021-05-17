[![Github Actions CI][1]][2]
[![HoTT Zulip chat][3]][4]

[Homotopy Type Theory][5] is an interpretation of
Martin-Löf’s intensional type theory into abstract homotopy theory.
Propositional equality is interpreted as homotopy and type isomorphism as
homotopy equivalence. Logical constructions in type theory then correspond to
homotopy-invariant constructions on spaces, while theorems and even proofs in
the logical system inherit a homotopical meaning. As the natural logic of
homotopy, type theory is also related to higher category theory as it is used
e.g. in the notion of a higher topos.

The HoTT library is a development of homotopy-theoretic ideas in the Coq proof
assistant. It draws many ideas from Vladimir Voevodsky's [Foundations][6]
library (which has since been incorporated into the [UniMath][7] library) and
also cross-pollinates with the [HoTT-Agda][8] library. See also: [HoTT in
Lean2][9], [Spectral Sequences in Lean2][10], and [Cubical Agda][11].

More information about this library can be found in:

- _The HoTT Library: A formalization of homotopy type theory in Coq_, Andrej
  Bauer, Jason Gross, Peter LeFanu Lumsdaine, Mike Shulman, Matthieu Sozeau, Bas
  Spitters, 2016 [arXiv][12] [CPP17][13]

Other publications related to the library can be found
[here][14].

# Installation

The HoTT library is part of the [Coq
Platform][15] and can be installed using
the installation instructions there.

More detailed installation instructions are provided in the file
[INSTALL.md](/INSTALL.md).

# Usage

The HoTT library can be used like any other Coq library. If you wish to use the
HoTT library in your own project, make sure to put the following arguments in
your `_CoqProject` file:

```
-arg -noinit
-arg -indices-matter
```

For more advanced use such as contribution see [INSTALL.md](/INSTALL.md).

We recommend the following text editors:

 * [Emacs][16] together with [Proof General][17].
 * [CoqIDE][18] part of the [Coq Proof Assistant][19].
 * [Visual Studio Code][20] together with [VSCoq][21].

Other methods of developing in `coq` will work as long as the correct arguments
are passed.

# Contributing

Contributions to the HoTT library are very welcome! For style guidelines and
further information, see the file [STYLE.md](/STYLE.md).

# Licensing

The library is released under the permissive BSD 2-clause license, see the file
[LICENSE.txt](/LICENSE.txt) for further information. In brief, this means you
can do whatever you like with it, as long as you preserve the Copyright
messages. And of course, no warranty!

# Wiki

More information can be found in the [Wiki][22].


[1]: https://github.com/HoTT/HoTT/workflows/CI/badge.svg?branch=master
[2]: https://github.com/HoTT/HoTT/actions?query=workflow%3ACI+branch%3Amaster
[3]: https://img.shields.io/badge/zulip-join_chat-brightgreen.svg
[4]: https://hott.zulipchat.com/

[5]: http://homotopytypetheory.org/

[6]: https://github.com/vladimirias/Foundations
[7]: https://github.com/UniMath/UniMath
[8]: https://github.com/HoTT/HoTT-Agda
[9]: https://github.com/leanprover/lean2/tree/master/hott
[10]: https://github.com/cmu-phil/Spectral
[11]: https://agda.readthedocs.io/en/v2.6.0.1/language/cubical.html

[12]: https://arxiv.org/abs/1610.04591
[13]: http://cpp2017.mpi-sws.org/
[14]: https://github.com/HoTT/HoTT/wiki/Publications-based-on-the-HoTT-library
[15]: https://github.com/coq/platform/releases

[16]: http://www.gnu.org/software/emacs/
[17]: http://proofgeneral.inf.ed.ac.uk
[18]: https://coq.inria.fr/refman/practical-tools/coqide.html
[19]: https://github.com/coq/coq
[20]: https://code.visualstudio.com/
[21]: https://github.com/coq-community/vscoq

[22]: https://github.com/HoTT/HoTT/wiki