#!/bin/bash

sudo apt-get build-dep coq coqide || exit 1
sudo apt-get install liblablgtksourceview2-ocaml-dev autoconf unzip wget || exit 1

wget -nc "https://github.com/mattam82/coq/archive/IR.zip" || exit 1

wget -nc "https://github.com/SkySkimmer/HoTT/archive/with-IR.zip" || exit 1

wget -nc "https://github.com/SkySkimmer/HoTTClasses/archive/CPP2017.zip" || exit 1

unzip -u IR.zip || exit 1
unzip -u with-IR.zip || exit 1
unzip -u CPP2017.zip || exit 1

cd coq-IR || exit 1
./configure -local || exit 1
make -j 2 coqlight coqide || exit 1
export PATH=$(pwd)"/bin:$PATH" || exit 1 #for coq_makefile for HoTTClasses, note that stable coq's coq_makefile works fine if you have it installed

cd ../HoTT-with-IR || exit 1
./autogen.sh || exit 1
./configure COQBIN=$(pwd)"/../coq-IR/bin" || exit 1
make -j 2 || exit 1
export PATH=$(pwd)":$PATH" || exit 1

cd ../HoTTClasses-CPP2017 || exit 1
./configure || exit 1
make -j 2 || exit 1



