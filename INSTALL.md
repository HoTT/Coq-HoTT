# INSTALLATION via OPAM

After installing Coq via opam [1]. One can install our version of Coq by:
```
   opam install coq.dev
```

However, one still needs to install the library via git to contribute.
Opam support on windows is experimental.
[1]: https://coq.inria.fr/opam/www/using.html

We are compatible with [Coq 8.10](https://github.com/coq/coq/releases/tag/V8.10.0),
so binary packages can be used.  Paths still need to be set manually.


# GENERAL INSTALLATION INSTRUCTIONS

1. Make sure you have all the prerequisites for compiling Coq. These are
   `OCaml`, `camlp5`, `git`, and `make`. If you want to build the HoTT
   version of the graphical user interface `coqide` you also need the
   `lablgtk2` and `lablgtksourceview2` libraries.  To get these:

   * Linux and OSX: Git and make can be installed through your package
     manager.  On Debian or any distribution with `apt-get` you can
     run the script `./etc/install_coq_deps.sh` in the HoTT directory
     (see step 2) which installs some dependencies automatically.
		 On OSX you can use the brew package manager:

         brew install opam
         opam init

     After that, you'll need to install a number of packages through `brew`
     and `opam`

         brew update
         brew install pkgconfig automake autoconf
         brew install libffi libxml2
         brew install lablgtk gtksourceview
         export PKG_CONFIG_PATH="/usr/local/opt/libffi/lib/pkgconfig:/usr/local/opt/libxml2/lib/pkgconfig:/usr/local/opt/gtksourceview/lib/pkgconfig"

		 However, for installing OCaml and its utilities we highly
     recommend using the Opam package manager for Ocaml
     (https://opam.ocaml.org/doc/Install.html).  Use opam2, and then
     install a recent version of Ocaml with
     
         opam init
         eval `opam env`
         opam switch create 4.06.1
         eval `opam env`
         opam install ocamlfind num
         opam install conf-gtksourceview lablgtk

   * MS Windows: [Note that these instructions have not been updated
     for a while, they may be out of date.  If you have trouble,
     please open an issue on the repository github tracker.]

	 	 We recommend that you install the 32-bit version of
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

   Even better, if you would like to contribute to HoTT, first fork the repository
   on github.com and then use your own fork. This way you will be able to make pull
   requests.

   If you do not want to deal with `git` at all, you may download an archive of HoTT
   at https://github.com/HoTT/HoTT/archive/master.zip and unpack that. We do not
   recommend this option because the HoTT library is under heavy development and
   you want to be able to easily track changes. Additionally, downloading the
   archive requires a working version of the `autoreconf` utility.

3. Install Coq.  The recommended option is to install a local/custom
   version of Coq in a subdirectory of the HoTT directory, which can be
   done by running from the HoTT directory:

        etc/install_coq.sh

   Compiling Coq may take a while.
   To speed it up, use `make -jn`, where n is the number of cores you have on your machine.
   On Linux this can be found with `nproc` or `lscpu`.
   On OSX Apple menu -> About this Mac -> System Report, then look for "number of cores".

	 Alternatively, you can install Coq using a package manager or opam.
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

4. Configure and build the HoTT Library.  If you installed the local
   version of Coq, then from the HoTT directory run the following
   commands:

        ./autogen.sh
        ./configure COQBIN="`pwd`/coq-HoTT/bin"
        make

	 If instead you installed a version of Coq that is available on your
	 PATH, you can omit the COQBIN argument to `configure`.  If you
	 installed a version of Coq that is not available on your PATH, then
	 you need to supply the *absolute* path name (starting with /) of
	 the `bin` directory which contains `coqtop`, `coqc`, etc.

5. Because it is a bit tricky to run Coq with a custom standard
   library, we provide scripts `hoqtop` and `hoqc` that do this for
   you, so you can run

       ./hoqtop

   directly from the HoTT directory to start using the library.  You
   can load the library from your Coq files with

       Require Import HoTT.

   There is also a `hoqc` for compiling files, and `hoqide` which is
   the version of coqide running the hoqtop toplevel if you have
   compiled it successfully.

	 You may prefer to install `hoqtop`, `hoqc` and the library files
   globally, in which case you can type

       sudo make install

   By default the files will be installed in `/usr/local/bin` and
   `/usr/local/share/hott`.  You can change the location by using
   standard `configure` parameters when you run it.  For example

       ./configure --bindir=$HOME/bin --datadir=$HOME/stuff

   will install `hoqtop` and `hoqc` in the `bin` subdirectory of your
   home directory and the HoTT library in `stuff/hott` subdirectory of
   your home directory.

6. If you use ProofGeneral (PG) for browsing existing theories, it
   should just work. But in case you want to create theories outside
   the `HoTT/theories` directory, do not forget to change the name of
   the Coq program called by PG. For instance you can edit the name of
   the executable called by PG by typing `M-x customize-variable`,
   then `coq-prog-name` or `proof-prog-name` which displays a
   customization utility.

   Another option is `M-x customize-variable` then
   `proof-prog-name-ask`, then click on the `Toggle` button in front
   of `Proof Prog Name Ask` and to save this for future sessions.
   This will prompt PG to ask you for the name of the Coq toplevel to
   be used each time you start evaluating a file.

7. To use the Emacs tags facility with the `*.v` files here, run the command

        make TAGS

   (The Emacs command `M-x find-tag`, bound to `M-.` , will take you to
   a definition or theorem, the default name for which is located under
   your cursor. Read the help on that Emacs command with `C-h k M-.` ,
   and learn the other facilities provided, such as the use of `M-*` to
   get back where you were, or the use of `M-x tags-search` to search
   throughout the code for locations matching a given regular
   expression.)

8. To prevent Emacs from prompting you about risky local variables
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

9. To update the library to the most current version, run `git pull`.
   You will then have to recompile it with `make`.

   If you have problems, you can try running `make clean` first, which
   removes all old compiled files.  This might be necessary if the
   library was reorganized.

   If you still have problems, it could be because the library was
   updated to use a newer version of Coq.  In this case you will have
   to re-run `etc/install_coq.sh`.

In case of any problems, feel free to contact us by opening an issue at
https://github.com/HoTT/HoTT.
