We recommend [installation using opam](#2-installation-of-hott-library-using-opam) if you wish to install the HoTT
library to use in your own project or to play around with.

## Table of contents

- [1. Using the HoTT library](#1-using-the-hott-library)
- [2. Installation of HoTT library using opam](#2-installation-of-hott-library-using-opam)
  - [Released Versions](#released-versions)
  - [Source Versions](#source-versions)
  - [Development Versions](#development-versions)
- [3. Setup for developers (using git)](#3-setup-for-developers-using-git)
  - [3.1. Prerequisites (Installing Rocq)](#31-prerequisites-installing-rocq)
    - [3.1.1. Development in OSX and Windows](#311-development-in-osx-and-windows)
  - [3.2. Forking and obtaining the HoTT library](#32-forking-and-obtaining-the-hott-library)
  - [3.3. Building the HoTT library](#33-building-the-hott-library)
  - [3.4. Installing the library using git](#34-installing-the-library-using-git)
- [4. Editors](#4-editors)
  - [4.1. Tags for Emacs](#41-tags-for-emacs)
- [5. Updating the library](#5-updating-the-library)
- [6. Troubleshooting](#6-troubleshooting)

# 1. Using the HoTT library

In order to use the HoTT library in your project, make sure you have a file
called `_CoqProject` in your working directory which contains the following
lines:

```
-arg -noinit
-arg -indices-matter
```

This way when you open `.v` files using `rocqide` or any other text editor for
Rocq (see [Editors](#4-editors)), the editor will pass the correct arguments to
Rocq.

To import modules from the HoTT library inside your own file, you will need to
write the following:

```coq
From HoTT Require Import Basics.
```

This, for example, will import the `Basics` module from the HoTT library. If you
wish to import the entire library you can write:

```coq
From HoTT Require Import HoTT.
```

# 2. Installation of HoTT library using opam

## Released Versions

To install the HoTT library via `opam`, first [install opam][3] and add the
released Rocq opam archive as follows:
```shell
$ opam repo add rocq-released https://rocq-prover.org/opam/released
```
This will let you install the released versions of the library. We typically do
a release for each major version of Rocq. The opam package is still named
`coq-hott`.

```shell
$ opam install coq-hott
```

## Source Versions

After cloning the repository, you can install the library using `opam` by running
`opam install .` in the root of the repository.

## Development Versions

We also have the current development version of the library available via
`opam`. Add the development repositories and install the package as follows:
```shell
$ opam repo add rocq-core-dev https://rocq-prover.org/opam/core-dev
$ opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev
$ opam install coq-hott.dev
```

The `coq-hott.dev` package requires the development version of Rocq. To use a
released version of Rocq with the library's current sources, follow the
[Source Versions](#source-versions) instructions instead.

# 3. Setup for developers (using git)

## 3.1. Prerequisites (Installing Rocq)

The required Rocq and Dune versions are listed in the
[package dependencies](../coq-hott.opam.template).
We recommend that you use the `opam` package manager to install Rocq. Details
about [installing Opam can be found here][3].
We also recommend working within an [opam switch][20], to keep your work
isolated from other packages installed via opam.

After setting up a switch (if you choose to do so), install Rocq with:

```shell
$ opam install rocq-core
```

You will also need `make` and `git` in a typical workflow. For Dune builds,
install Dune with `opam install dune`.


### 3.1.1. Development in OSX and Windows

We don't recommend developing on platforms other than Linux, however it is still
possible.

Windows and OSX users can find additional setup instructions in the
[Rocq installation guide][9].

For OSX users `git` and `make` should be readily available.

Windows users can install [`git` as described here][18] and [`make` as described
here][17].

## 3.2. Forking and obtaining the HoTT library

In order to do development on the HoTT library, we recommend that you [fork it
on Github][4]. More details [about forking can be found here][5].

Use `git` to clone your fork locally:

```shell
$ git clone https://github.com/YOUR-USERNAME/HoTT
```

Of course, you may clone the library directly, but for development it is
recommended to work on a fork.

To follow the rest of the instructions, it is best to change your working
directory to the `HoTT` directory.

```shell
$ cd HoTT
```

We also recommend that you [add the main repository as a git remote][6]. This
makes it easier to track changes happening on the main repository. This can be
done as follows:
```shell
$ git remote add upstream https://github.com/HoTT/HoTT.git
```

## 3.3. Building the HoTT library

In order to compile the files of the HoTT library, run `make`:

```shell
$ make
```
You can speed up the build by passing `-jN` where `N` is the number of parallel
recipes `make` will execute.

You can also use `dune` to build the library.

```shell
$ dune build
```

## 3.4. Installing the library using git

When developing HoTT itself, build in the checkout; installation is not needed.
To use your checkout from a separate project, install it with:

```shell
$ make install
```

# 4. Editors

We recommend the following text editors for the development of `.v` files:

 * [Emacs][10] together with [Proof General][11].
 * [RocqIDE][12] part of the [Rocq Proof Assistant][13].
 * [Visual Studio Code][14] together with [coq-lsp][15].
 * For more editors, see the Rocq website's [installation guide][19].

## 4.1. Tags for Emacs

To use the Emacs tags facility with the `*.v` files here, run the command:
```shell
$ make TAGS
```
The Emacs command `M-x find-tag`, bound to `M-.` , will take you to a definition
or theorem, the default name for which is located under your cursor. Read the
help on that Emacs command with `C-h k M-.` , and learn the other facilities
provided, such as the use of `M-*` to get back where you were, or the use of
`M-x tags-search` to search throughout the code for locations matching a given
regular expression.

Dune users may use the following to generate tags:

```shell
dune build TAGS
```

# 5. Updating the library

If you installed the library via `opam` then simply run `opam update` and then
`opam upgrade`.

To upgrade your clone of the GitHub repository as set up in [the instructions on
using git](#32-forking-and-obtaining-the-hott-library): Pull the latest version
using `git pull upstream master` and then rebuild using `make` as above.

To update your fork, use `git push origin master`. We also [have tags in the
GitHub repository][7] for our released versions which you can use instead of
`master`.

# 6. Troubleshooting

In case of any problems, feel free to contact us by [opening an issue on
GitHub](https://github.com/HoTT/HoTT).


[3]: https://opam.ocaml.org/doc/Install.html
[4]: https://github.com/HoTT/HoTT
[5]: https://docs.github.com/en/github/getting-started-with-github/fork-a-repo

[6]: https://docs.github.com/en/github/collaborating-with-issues-and-pull-requests/configuring-a-remote-for-a-fork
[7]: https://github.com/HoTT/HoTT/releases
[8]: https://opam.ocaml.org/doc/Install.html#OSX
[9]: https://rocq-prover.org/install
[10]: http://www.gnu.org/software/emacs/

[11]: http://proofgeneral.inf.ed.ac.uk
[12]: https://rocq-prover.org/refman/practical-tools/coqide.html
[13]: https://github.com/rocq-prover/rocq
[14]: https://code.visualstudio.com/
[15]: https://github.com/ejgallego/coq-lsp

[16]: https://cygwin.com/install.html
[17]: https://stackoverflow.com/a/54086635
[18]: https://git-scm.com/book/en/v2/Getting-Started-Installing-Git
[19]: https://rocq-prover.org/install

[20]: https://ocaml.org/docs/opam-switch-introduction
