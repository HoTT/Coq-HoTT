#!/usr/bin/env bash

PS4='$ '
set -x

NJOBS=1
sudo apt-get install -q opam camlp5 camlp4 ocaml-findlib libocamlgraph-ocaml-dev
[ -e .opam ] || opam init -j ${NJOBS} --compiler=system -n -y
eval $(opam config env)
opam config var root
opam install -j ${NJOBS} -y camlp5 ocamlfind ocamlgraph
opam list
