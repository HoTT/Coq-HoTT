# -j2 causes a bug in caml compiler, I believe while accessing/creating the
# same file in parallel 
MAKEFLAGS := -r #-j2

.SUFFIXES:

.PHONY: clean all tags install

VERSION := $(shell grep 'let ssrversion' src/ssreflect.ml4 | cut -d \" -f 2)
COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	mkdir -p bin
	$(COQMAKE) all

$(COQMAKEFILE): Make
	$(COQBIN)coq_makefile -f Make  > $(COQMAKEFILE)

tags:
	$(COQBIN)coqtags `find . -name \*.v`

install:
	$(COQMAKE) install

clean:
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)
	rm -rf ssreflect-$(VERSION) ssreflect-$(VERSION).tar.gz
	rm -rf test-dist-static test-dist-dynamic

dist:
	# VERSION is computed reading src/ssreflect.ml, line let ssrversion
	rm -rf ssreflect-$(VERSION)
	svn export . ssreflect-$(VERSION)
	# files in the svn, but not meant to be part of the release
	rm ssreflect-$(VERSION)/description 
	rm ssreflect-$(VERSION)/src/Makefile
	rm ssreflect-$(VERSION)/NOTICE
	# checking for spurious or out of sync .v
	for X in ssreflect-$(VERSION)/theories/*.v; do\
	  if ! grep -q `basename $$X` ssreflect-$(VERSION)/Make; then\
	    echo "warning: `basename $$X` not listed in Make: removing it";\
	    rm $$X;\
	  fi;\
	  if ! diff $$X ../../`basename $$X` > /dev/null 2>&1; then\
	    echo "warning: theories/`basename $$X` and ../../`basename $$X`" \
	    	"differ";\
	  fi;\
	done
	# handling of NOTICE: All rights reserved -> released under XYZ
	for X in `find ssreflect-$(VERSION)/ -name \*.v -o -name \*.ml`; do\
		( head -1 $$X | grep -q 'All rights reserved' ) || \
			echo "warning: `basename $$X` with no reserved"\
		       		"copyrights";\
		sed -i -e '1rNOTICE' -e '/All rights reserved/D' $$X;\
	done
	# tarball + MANIFEST
	tar -cvf ssreflect-$(VERSION).tar ssreflect-$(VERSION)/ | \
	  sed 's/^[^\/]*\///' | grep -v '^$$' | grep -v '/$$' |\
	       	sort > MANIFEST
	mv MANIFEST ssreflect-$(VERSION)/MANIFEST
	tar -f ssreflect-$(VERSION).tar -r ssreflect-$(VERSION)/MANIFEST
	gzip -f9 ssreflect-$(VERSION).tar
	rm -rf ssreflect-$(VERSION)/

test-dist:
	rm -rf test-dist-static test-dist-dynamic
	mkdir test-dist-static
	mkdir test-dist-dynamic
	tar -xzf ssreflect-$(VERSION).tar.gz -C test-dist-static
	tar -xzf ssreflect-$(VERSION).tar.gz -C test-dist-dynamic
	sed -i 's/^#//' test-dist-static/ssreflect-$(VERSION)/Make
	make -C test-dist-static/ssreflect-$(VERSION) all test & P1=$$!; \
		make -C test-dist-dynamic/ssreflect-$(VERSION) all test & P2=$$!; \
		wait $$P1 && wait $$P2
	rm -rf test-dist-static test-dist-dynamic
