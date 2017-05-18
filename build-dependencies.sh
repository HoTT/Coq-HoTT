#!/usr/bin/env bash

set -x

echo 'Getting dependency archives...'
echo -en 'travis_fold:start:dep.get\\r'

wget -nc "https://github.com/mattam82/coq/archive/IR.zip" || exit 1
wget -nc "https://github.com/SkySkimmer/HoTT/archive/mz-8.7.zip" || exit 1

yes | unzip -u IR.zip || exit 1
yes | unzip -u mz-8.7.zip || exit 1

echo -en 'travis_fold:end:dep.get\\r'

echo 'Building Coq...'
echo -en 'travis_fold:start:coq.build\\r'

pushd coq-IR || exit 1
./configure -local || exit 1
make -j 2 tools coqbinaries pluginsopt states || exit 1
export PATH="$(pwd)/bin:$PATH" #for coq_makefile for HoTTClasses, note that stable coq's coq_makefile works fine if you have it installed
popd

echo -en 'travis_fold:end:coq.build\\r'

echo 'Building HoTT...'
echo -en 'travis_fold:start:HoTT.build\\r'

pushd HoTT-mz-8.7 || exit 1
./autogen.sh || exit 1
./configure COQBIN="$(pwd)/../coq-IR/bin/" || exit 1
make -j 2 || exit 1
export PATH="$(pwd):$PATH"
popd

echo -en 'travis_fold:end:HoTT.build\\r'
