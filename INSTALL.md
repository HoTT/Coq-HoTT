## Obtain Prerequisites

Make sure you have all the prerequisites for compiling Coq. These are
`OCaml`, `camlp5`, `git`, and `make`. If you want to build the HoTT
version of the graphical user interface `coqide` you also need the
`lablgtk3` and `lablgtksourceview3` libraries.  To get these:

### Linux and OSX

Git and make can be installed through your package manager.  On Debian
or any distribution with `apt-get` you can run the script
`./etc/install_coq_deps.sh` in the HoTT directory (see step 2) which
installs some dependencies automatically.

On OSX you can instead use the brew package manager:

    brew update
    brew install opam
    brew install pkgconfig automake autoconf
    brew install libffi libxml2
    brew install lablgtk gtksourceview
    export PKG_CONFIG_PATH="/usr/local/opt/libffi/lib/pkgconfig:/usr/local/opt/libxml2/lib/pkgconfig:/usr/local/opt/gtksourceview/lib/pkgconfig"

However, for installing OCaml and its utilities we highly recommend
using the Opam package manager for Ocaml [1] instead of your operating
system package manager.  Run `opam --version` to check that opam is
installed and up to date. If the opam version is less than 2, you
should install a recent version of opam using the curl command
provided at https://opam.ocaml.org/.

    sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

You can then initialize opam with
     
    opam init

It is recommended to allow opam to change your .profile file when it
asks for permission.

After that switch to ocaml version 4.07.1 using

    opam switch create 4.07.1
    opam switch 4.07.1

You may also need to run

    eval `opam env`

to continue working in the same terminal.  Then you can install the
required dependencies:

    opam install ocaml camlp5 lablgtk3 lablgtk3-sourceview3 ocamlfind num

[1]:https://opam.ocaml.org/doc/Install.html

### MS Windows

Here are some instruction for setting up the HoTT library using the
Coq precompiled binaries.

1. Install the [precompiled binaries for coq](https://github.com/coq/coq/releases). Just pick the one
labelled latest release and run the exe file.
2. Run the [cygwin installer](https://cygwin.com/install.html). It
doesn't matter which version, 64 and 32 both work.
3. When you are told to choose packages, select the following packages
(use the search bar)
  `git`, `make`, `ocaml`, `automake`, `libtool`
You can select these packages by choosing a version from the drop down
in the installer.
4. Complete the installation of cygwin.
5. Run cygwin and check that git works by running `git`. It should
just give you the help screen.

## Obtain the HoTT library

Of course, skip this step if you already have it.  The most
straightforward way to download it is

    git clone https://github.com/HoTT/HoTT.git
    cd HoTT

If you would like to contribute to the library (or imagine that you
might one day in the future), we recommend that you first fork the
repository on github.com and then clone your own fork. This way you
will be able to make pull requests.

If you do not want to deal with `git` at all, you may download an
archive of HoTT at https://github.com/HoTT/HoTT/archive/master.zip and
unpack that. We do not recommend this option because the HoTT library
is under heavy development and you want to be able to easily track
changes. Additionally, downloading the archive requires a working
version of the `autoreconf` utility.

A somewhat old version of the HoTT library is also available on opam
as `coq-hott` in the "extra-dev" archive
(https://github.com/coq/opam-coq-archive/tree/master/extra-dev).
However, to obtain an up-to-date version of the library, and to
contribute to it, you need to clone it using git.


## Install Coq (Linux and OSX)

The recommended procedure is to install a local/custom version of Coq
in a subdirectory of the HoTT directory, which can be done by running
from the HoTT directory:

    etc/install_coq.sh

Compiling Coq may take a while.
To speed it up, use `make -jn`, where n is the number of cores you
have on your machine.
On Linux this can be found with `nproc` or `lscpu`.
On OSX Apple menu -> About this Mac -> System Report, then look for
"number of cores".

Alternatively, you can install Coq using a package manager or opam.

If you get error messages during the compilation of Coq about the
command line option "-fno-defer-pop", then you might be running Mac OS
X 10.9 with an ocaml compiler installed by "brew".  We recommend
installing ocaml using opam instead, as described above.

If you don't want to compile your own copy of Coq, then the HoTT
library is compatible with [Coq
8.12](https://github.com/coq/coq/releases/tag/V8.12.0), so you can
also install a binary Coq package using a package manager or opam.
Paths still need to be set manually.  On Debian/Ubuntu, you can also
install the master development branch of Coq as your only version of
Coq if you want:

        sudo add-apt-repository ppa:jgross-h/coq-master-daily
        sudo apt-get update
        sudo apt-get install coq


## Configure and build the HoTT Library

If you installed the local version of Coq, then from the HoTT
directory run the following commands:

    ./autogen.sh
    ./configure COQBIN="`pwd`/coq-HoTT/bin"
    make

If instead you installed a version of Coq that is available on your
PATH, you can omit the COQBIN argument to `configure`.  If you
installed a version of Coq that is not available on your PATH, then
you need to supply the *absolute* path name (starting with /) of the
`bin` directory which contains `coqtop`, `coqc`, etc.

If you are trying to install on Windows using cygwin, configure the 
library with `./configure COQBIN="/cygdrive/c/Coq/bin/"`. This tells 
the HoTT library where to find the coq binaries. This is of course 
assuming the coq binaries were installed in `C:\Coq\bin`. When in 
cygwin you can access your C drive through `/cygdrive/c`.

## Running Coq for the HoTT library

Because it is a bit tricky to run Coq with a custom standard library,
we provide scripts `hoqtop` and `hoqc` that do this for you, so you
can run

    ./hoqtop

directly from the HoTT directory to start using the library.
You can load the library from your Coq files with

    Require Import HoTT.

There is also a `hoqc` for compiling files, and `hoqide` which is the
version of coqide running the hoqtop toplevel if you have compiled it
successfully.

You may want to put an ampersand after `./hoqide &` to allow the
process to run in the background, allowing you to continue using the
terminal.

You may prefer to install `hoqtop`, `hoqc` and the library files
globally, in which case you can type

    sudo make install

Though this is not recommended if you intend on developing the library
itself.

By default the files will be installed in `/usr/local/bin` and
`/usr/local/share/hott`.  You can change the location by using
standard `configure` parameters when you run it.  For example

    ./configure --bindir=$HOME/bin --datadir=$HOME/stuff

will install `hoqtop` and `hoqc` in the `bin` subdirectory of your
home directory and the HoTT library in `stuff/hott` subdirectory of
your home directory.


## Using Emacs and Proof General

If you use ProofGeneral (PG) for browsing existing theories, it should
just work. But in case you want to create theories outside the
`HoTT/theories` directory, do not forget to change the name of the Coq
program called by PG. For instance you can edit the name of the
executable called by PG by typing `M-x customize-variable`, then
`coq-prog-name` or `proof-prog-name` which displays a customization
utility.

Another option is `M-x customize-variable` then `proof-prog-name-ask`,
then click on the `Toggle` button in front of `Proof Prog Name Ask`
and to save this for future sessions.  This will prompt PG to ask you
for the name of the Coq toplevel to be used each time you start
evaluating a file.

To use the Emacs tags facility with the `*.v` files here, run the
command

    make TAGS

(The Emacs command `M-x find-tag`, bound to `M-.` , will take you to a
definition or theorem, the default name for which is located under
your cursor. Read the help on that Emacs command with `C-h k M-.` ,
and learn the other facilities provided, such as the use of `M-*` to
get back where you were, or the use of `M-x tags-search` to search
throughout the code for locations matching a given regular
expression.)

To prevent Emacs from prompting you about risky local variables every
time you open a `*.v` file, you can inform it that the variables we
use are safe.  In newer versions of Emacs, you can do this by simply
pressing `!` at the prompt.  In older versions of Emacs, that option
is not available; instead you can add the following lisp form to the
Emacs variable `safe-local-eval-forms`.  One way to do this is to run
`M-x customize-variable`, enter `safe-local-eval-forms`, click `INS`
and paste in the following lisp form, then click `State` and select
`Save for future sessions`.

    (let ((default-directory
           (locate-dominating-file buffer-file-name ".dir-locals.el")))
      (make-local-variable 'coq-prog-name)
      (setq coq-prog-name (expand-file-name "../hoqtop")))


## Updating the library

To update the library to the most current version, run `git pull`.
You will then have to recompile it with `make`.

If you have problems, you can try running `make clean` first, which
removes all old compiled files.  This might be necessary if the
library was reorganized.

If you still have problems, it could be because the library was
updated to use a newer version of Coq.  Assuming you have compiled a
local copy of Coq, the following commands should update it:

    git pull
    git submodule update
    opam update
    opam upgrade
    etc/install_coq.sh
    make

In case of any problems, feel free to contact us by opening an issue at
https://github.com/HoTT/HoTT.
