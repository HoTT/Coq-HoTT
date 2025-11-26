We recommend [these install instructions](#1-installation-using-coq-platform) if you wish to install the HoTT
library to use in your own project or to play around with.

## Table of contents

- [1. Installation using Coq Platform](#1-installation-using-coq-platform)
- [2. Installation of HoTT library using opam](#2-installation-of-hott-library-using-opam)
  - [Released Versions](#released-versions)
  - [Source Versions](#source-versions)
  - [Development Versions](#development-versions)
- [3. Setup for developers (using git)](#3-setup-for-developers-using-git)
  - [3.1. Prerequisites (Installing Coq)](#31-prerequisites-installing-coq)
    - [3.1.1. Development in OSX and Windows](#311-development-in-osx-and-windows)
  - [3.2. Forking and obtaining the HoTT library](#32-forking-and-obtaining-the-hott-library)
  - [3.3. Building the HoTT library](#33-building-the-hott-library)
  - [3.4. Installing the library using git](#34-installing-the-library-using-git)
- [4. Editors](#4-editors)
  - [4.1. Tags for Emacs](#41-tags-for-emacs)
- [5. Updating the library](#5-updating-the-library)
- [6. Troubleshooting](#6-troubleshooting)

# 1. Installation using Coq Platform

**Note:** As of version 9.0, Coq has been renamed Rocq.  When you install Coq-HoTT
following the instructions in this section, it should automatically
install the compatibility wrappers, so that the nothing about the build process
needs to change.

In order to install the HoTT library, we recommend that you use the [Coq
Platform][1]. This will install the [Coq Proof Assistant][2] together with the
HoTT library. The Coq Platform supports installation on **Linux**, **MacOS** and
**Windows**.

In order to use the HoTT library in your project, make sure you have a file
called `_CoqProject` in your working directory which contains the following
lines:

```
-arg -noinit
-arg -indices-matter
```

This way when you open `.v` files using `coqide` or any other text editor for
coq (see [Editors](#editors)), the editor will pass the correct arguments to
`coq`.

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

> ### Warning
>
> The versions of the HoTT library appearing in the Coq Platform are released
> twice a year. This means that there is a good chance that the Coq Platform
> version is lagging behind the latest version of the library. If you wish to
> use the latest version of the library, you should install it using `opam` as
> described in the next section.

# 2. Installation of HoTT library using opam

**Note:** As of version 9.0, Coq has been renamed Rocq.  When you install Coq-HoTT
following the instructions in this section, it should automatically
install the compatibility wrappers, so that the nothing about the build process
needs to change.

## Released Versions

More advanced users may wish to install the HoTT library via `opam` ([See here
for details on installing `opam`][3]). You need to add the released coq-archive
packages to `opam` which can be done as follows:
```shell
$ opam repo add coq-released https://coq.inria.fr/opam/released
```
This will let you install the released versions of the library. We typically do
a release for each major version of `coq`. Note that the name of the HoTT
library is `coq-hott` inside the coq-archive.

```shell
$ opam install coq-hott
```

## Source Versions

After cloning the repository, you can install the library using `opam` by running
`opam install .` in the root of the repository.

## Development Versions

We also have the current development versions of the library available via
`opam`. For this however, you will need to add the dev coq-archive packages:
```shell
$ opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
$ opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```

This will make `coq.dev` the latest available version of `coq`. You can pin
`coq` to a stable version by running `opam pin add coq.dev 8.19.1` for example.
Then install the library with `opam install coq-hott`, as for the released version.

# 3. Setup for developers (using git)

## 3.1. Prerequisites (Installing Coq)

We recommend that you use the `opam` package manager to install `coq`. Details
about [installing Opam can be found here][3].
We also recommend working within an [opam switch][20], to keep your work
isolated from other packages installed via opam.

After setting up a switch (if you choose to do so),
you can install the latest 8.x version of `coq` by doing the following:

```shell
$ opam install coq
```

To install the latest 9.x version of Rocq and the Coq compatibility wrappers, do

```shell
$ opam install rocq-core coq-core
```

You will also need `make` and `git` in a typical workflow.


### 3.1.1. Development in OSX and Windows

We don't recommend developing on platforms other than Linux, however it is still
possible.

Windows and OSX users may install `coq` directly using the [installer for the
appropriate coq release][9].

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

We don't recommend you install the library using the repository and instead
recommend [installing via opam](#installation-of-hott-library-using-opam),
especially if you are intending to develop the library. However the `makefile`
contains a target called `install` and therefore running
```shell
$ make install
```
will install the library.

# 4. Editors

We recommend the following text editors for the development of `.v` files:

 * [Emacs][10] together with [Proof General][11].
 * [CoqIDE][12] part of the [Coq Proof Assistant][13].
 * [Visual Studio Code][14] together with [coq-lsp][15].
 * For more editors, see the Coq website article on [User Interfaces][19].

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
If you installed the library via Coq Platform then [update your version of Coq
Platform][1].

If you installed the library via `opam` then simply run `opam update` and then
`opam upgrade`.

To upgrade your clone of the GitHub repository as set up in [the instructions on
using git](#forking-and-obtaining-the-hott-library): Pull the latest version
using `git pull upstream master` and then rebuild using `make` as above.

To update your fork, use `git push origin master`. We also [have tags in the
GitHub repository][7] for our released versions which you can use instead of
`master`.

# 6. Troubleshooting

In case of any problems, feel free to contact us by [opening an issue on
GitHub](https://github.com/HoTT/HoTT).


[1]: https://github.com/coq/platform/releases
[2]: https://github.com/coq/coq
[3]: https://opam.ocaml.org/doc/Install.html
[4]: https://github.com/HoTT/HoTT
[5]: https://docs.github.com/en/github/getting-started-with-github/fork-a-repo

[6]: https://docs.github.com/en/github/collaborating-with-issues-and-pull-requests/configuring-a-remote-for-a-fork
[7]: https://github.com/HoTT/HoTT/releases
[8]: https://opam.ocaml.org/doc/Install.html#OSX
[9]: https://github.com/coq/coq/releases
[10]: http://www.gnu.org/software/emacs/

[11]: http://proofgeneral.inf.ed.ac.uk
[12]: https://coq.inria.fr/refman/practical-tools/coqide.html
[13]: https://github.com/coq/coq
[14]: https://code.visualstudio.com/
[15]: https://github.com/ejgallego/coq-lsp

[16]: https://cygwin.com/install.html
[17]: https://stackoverflow.com/a/54086635
[18]: https://git-scm.com/book/en/v2/Getting-Started-Installing-Git
[19]: https://coq.inria.fr/user-interfaces.html

[20]: https://ocaml.org/docs/opam-switch-introduction
