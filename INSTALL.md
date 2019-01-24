# INSTALLATION via OPAM

After installing Coq via opam [1]. One can install our version of Coq by:
```
   opam install coq.dev
```

However, one still needs to install the library via git to contribute.
Opam support on windows is experimental.
[1]: https://coq.inria.fr/opam/www/using.html

We will be compatible with [Coq 8.10](https://github.com/coq/coq/releases/tag/V8.10.0), so binary packages can be used once it is released.  Until then, the development version of Coq must be installed. Either way, paths still need to be set manually.


# QUICK INSTALLATION INSTRUCTIONS

If you are not a Coq expert and just want to get the HoTT library to work with
minimal fuss, you should try your luck by following these instructions:

1. Make sure you have all the prerequisites for compiling Coq. These are
   `OCaml`, `camlp5`, `git`, and `make`. If you want to build the HoTT
   version of the graphical user interface `coqide` you also need the
   `lablgtk2` and `lablgtksourceview2` libraries. To get these:

   * Linux: check your package manager. On Debian or any distribution
     with `apt-get` you can run the script `./etc/install_coq_deps.sh`
     which installs the dependencies automatically.

   * OSX: we recommend that you install the Opam package manager for Ocaml
     (http://opam.ocamlpro.com/) and go from there.

         brew install opam
         brew update; brew upgrade objective-caml

   * MS Windows: we recommend that you install the 32-bit version of
     cygwin (installer at http://www.cygwin.com/setup-x86.exe) and,
     in the setup process install all of the packages mentioning
     `ocaml`, as well as `make` and `git` and `dos2unix`.  (The 64-bit
     version of cygwin seems to be missing some ocaml packages.  See
     also https://coq.inria.fr/bugs/show_bug.cgi?id=3154.)  To prevent
     bash from complaining about unrecognized `\r` commands, use
     `dos2unix`.  The following commands, from the root of the HoTT
     library, should mostly take care of things:

         dos2unix hoq*
         /usr/bin/find . -name '*.sh' | xargs dos2unix

     If you wish to build CoqIDE/hoqide on Windows, we wish you good luck.
2. Get the HoTT library (skip this step if you already have it):

        git clone https://github.com/HoTT/HoTT.git
        cd HoTT

3. From the HoTT directory run the following commands:

        etc/install_coq.sh
        ./autogen.sh
        ./configure COQBIN="`pwd`/coq-HoTT/bin"
        make

   It may take a while to compile the custom Coq. To speed this up, use `make -jn`, where n is the number of cores you have on your machine.
   On linux this can be found with `nproc` or `lscpu`.
   On OSX Apple menu -> About this Mac -> System Report, then look for "number of cores"

   If you are using Debian/Ubuntu, and don't mind having coq master
   as your only version of Coq, you can install it using apt-get:

        sudo add-apt-repository ppa:jgross-h/coq-master-daily
        sudo apt-get update
        sudo apt-get install coq

   If you get error messages during the compilation of Coq about the command
   line option "-fno-defer-pop", then you might be running Mac OS X 10.9 with
   an ocaml compiler installed by "brew".  In that case try

       brew update; brew upgrade objective-caml

   If that doesn't work, try

       brew remove objective-caml; brew install objective-caml

4. You can now use the HoTT library in place by running `./hoqtop` and
   `./hoqc`. You can also use `./hoqide` which is the version of coqide
   running the hoqtop toplevel if you have compiled it successfully.  If you
   want the commands `hoqtop`, `hoqc`, `hoqide` available system-wide, run:

        make install

   The library can be loaded into a Coq session with `Require Import HoTT.`

5. If you use ProofGeneral (PG) for browsing existing theories, it should just
   work. But in case you want to create theories outside the `HoTT/theories`
   directory, do not forget to change the name of the Coq
   program called by PG. For instance you can edit the name of the executable
   called by PG by typing `M-x customize-variable`, then `coq-prog-name` which
   displays a customization utility. Another option is to type `M-x
   customize-variable`, then `proof-prog-name-ask`, to click on the `Toogle`
   button in front of `Proof Prog Name Ask` and to save this for future sessions.
   This will prompt PG to ask you for the name of the Coq toplevel to be used
   each time you start evaluating a file.

6. To use the Emacs tags facility with the `*.v` files here, run the command

        make TAGS

   (The Emacs command `M-x find-tag`, bound to `M-.` , will take you to
   a definition or theorem, the default name for which is located under
   your cursor. Read the help on that Emacs command with `C-h k M-.` ,
   and learn the other facilities provided, such as the use of `M-*` to
   get back where you were, or the use of `M-x tags-search` to search
   throughout the code for locations matching a given regular
   expression.)

7. To prevent Emacs from prompting you about risky local variables
   every time you open a `*.v` file, you can inform it that the
   variables we use are safe.  In newer versions of Emacs, you can do
   this by simply pressing `!` at the prompt.  In older versions of
   Emacs, that option is not available; instead you can add the
   following lisp form to the Emacs variable `safe-local-eval-forms`.
   One way to do this is to run `M-x customize-variable`, enter
   `safe-local-eval-forms`, click `INS` and paste in the following
   lisp form, then click `State` and select `Save for future
   sessions`.

        (let ((default-directory
               (locate-dominating-file buffer-file-name ".dir-locals.el")))
          (make-local-variable 'coq-prog-name)
          (setq coq-prog-name (expand-file-name "../hoqtop")))

8. To update the library to the most current version, run `git pull`.
   You will then have to recompile it with `make`.

   If you have problems, you can try running `make clean` first, which
   removes all old compiled files.  This might be necessary if the
   library was reorganized.

   If you still have problems, it could be because the library was
   updated to use a newer version of Coq.  In this case you will have
   to re-run `etc/install_coq.sh`.

In case of any problems, feel free to contact us by opening an issue at
https://github.com/HoTT/HoTT.


# DETAILED INSTALLATION INSTRUCTIONS

## INSTALLATION OF HoTT

Clone the HoTT repository with

    git clone https://github.com/HoTT/HoTT.git

Even better, if you would like to contribute to HoTT, first fork the repository
on github.com and then use your own fork. This way you will be able to make pull
requests.

If you do not want to deal with `git` at all, you may download an archive of HoTT
at https://github.com/HoTT/HoTT/archive/master.zip and unpack that. We do not
recommend this option because the HoTT library is under heavy development and
you want to be able to easily track changes. Additionally, downloading the
archive requires a working version of the `autoreconf` utility.

### PREREQUISITES

The HoTT library requires the command-line option `-indices-matter`. This
changes the interpretation of equality to one that conforms to the
homotopy-theoretic interpretation.

### Configuration of the HoTT library

To configure the HoTT library:

1. If Coq can be found in PATH, run

       ./autogen.sh
       ./configure

   in the HoTT directory.

2. If you installed Coq somewhere special or configured it
   with `-local`, you should tell `./configure` where to find Coq:

       ./autogen.sh
       ./configure COQBIN=<directory-containing-coq-executables>

   where you should specify the *absolute* path name (starting with /)
   of the directory which contains `coqtop`, `coqc`, etc.

To compile the HoTT library type

    make

Because it is a bit tricky to run Coq with a custom standard library,
we provided scripts `hoqtop` and `hoqc` that do this for you, so you
can run

    ./hoqtop

directly from the HoTT directory to start using the library. Load it
with

    Require Import HoTT.

There is also `hoqc` for compiling files. You may prefer to install
`hoqtop`, `hoqc` and the library files globally, in which case you
type

    sudo make install

By default the files will be installed in `/usr/local/bin` and
`/usr/local/share/hott`.  You can change the location by using
standard `configure` parameters when you run it.  For example

    ./configure --bindir=$HOME/bin --datadir=$HOME/stuff

will install `hoqtop` and `hoqc` in the `bin` subdirectory of your
home directory and the HoTT library in `stuff/hott` subdirectory of
your home directory.

If you are using ProofGeneral (PG), do not forget to change the name
of the Coq program called by PG. For instance you can edit the name of
the executable called by PG by typing 'M-x customize-variable', then
'proof-prog-name' which displays a customization utility. An other
option is to type 'M-x customize-variable', then
'proof-prog-name-ask', to click on the 'Toogle' button in front of
Proof Prog Name Ask and to save this for future sessions. This will
prompt PG to ask you for the name of the coq toplevel to be used each
time you start evaluating a file.
