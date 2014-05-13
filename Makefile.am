ACLOCAL_AMFLAGS = -I etc

bin_SCRIPTS = hoqtop hoqc hoq-run
if make_hoqide
  bin_SCRIPTS += hoqide
endif
if make_hoqtopbyte
  bin_SCRIPTS += hoqtop.byte
endif

hottdir=$(datarootdir)/hott
EXTRA_DIST = coq theories etc LICENSE.txt CREDITS.txt INSTALL.txt README.markdown

# The path to the Coq library in $(srcdir)
SRCCOQLIB=$(srcdir)/coq

# support the TIMED variable like coq_makefile
TIMED=
TIMECMD=
#STDTIME=@STDTIME@
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

# some makefile magic to make things like `make TIMED=1` less noisy
V = 0

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

SILENCE_HOQC_0 := @echo \"HOQC $$<\"; #
SILENCE_HOQC_1 :=
SILENCE_HOQC = $(SILENCE_HOQC_$(V))

SILENCE_COQDEP_0 := @echo \"COQDEP $$<\"; #
SILENCE_COQDEP_1 :=
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

# the proviola camera
CAMERA = python proviola/camera/camera.py

# include the makefile listing all the targets.  This way, we don't
# need to rerun configure every time we add a new file.  The targets
# makefile should provide CORE_VFILES and STD_VFILES and
# CATEGORY_VFILES.  To add more targets (e.g., ANALYSIS_VFILES), you'll
# need to update Makefile.am and run autogen.sh and configure again.

MAKEFILE_TARGETS_FILE = Makefile_targets.mk

include $(MAKEFILE_TARGETS_FILE)

# The list of files that comprise the HoTT library
CORE_VOFILES=$(CORE_VFILES:.v=.vo)
CORE_GLOBFILES=$(CORE_VFILES:.v=.glob)
CORE_DEPFILES=$(CORE_VFILES:.v=.d)
CORE_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html/HoTT.%,$(subst /,.,$(CORE_VFILES:.v=.html)))
CORE_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(CORE_HTMLFILES))
CORE_DPDFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/file-dep-graphs/HoTT.%,$(subst /,.,$(CORE_VFILES:.v=.dpd)))

# The list of files that comprise the category theory in the HoTT library
CATEGORY_VOFILES=$(CATEGORY_VFILES:.v=.vo)
CATEGORY_GLOBFILES=$(CATEGORY_VFILES:.v=.glob)
CATEGORY_DEPFILES=$(CATEGORY_VFILES:.v=.d)
CATEGORY_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html/HoTT.%,$(subst /,.,$(CATEGORY_VFILES:.v=.html)))
CATEGORY_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(CATEGORY_HTMLFILES))
CATEGORY_DPDFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/file-dep-graphs/HoTT.%,$(subst /,.,$(CATEGORY_VFILES:.v=.dpd)))

# The list of files from contrib
CONTRIB_VOFILES=$(CONTRIB_VFILES:.v=.vo)
CONTRIB_GLOBFILES=$(CONTRIB_VFILES:.v=.glob)
CONTRIB_DEPFILES=$(CONTRIB_VFILES:.v=.d)
CONTRIB_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).contrib.%,$(srcdir)/html/%,$(subst /,.,$(CONTRIB_VFILES:.v=.html)))
CONTRIB_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(CONTRIB_HTMLFILES))

# I'm not sure why we needs = rather than :=, but we seem to
ALL_BUILT_HOTT_VFILES = $(STD_VFILES) $(CORE_VFILES) $(CATEGORY_VFILES)
ALL_HOTT_VFILES = $(shell find "$(srcdir)/theories" -name "*.v") $(shell find "$(SRCCOQLIB)/theories" -name "*.v")
UNBUILT_VFILES = $(filter-out $(ALL_BUILT_HOTT_VFILES),$(ALL_HOTT_VFILES))

# The list of files that comprise the alternative standard library
STD_VOFILES=$(STD_VFILES:.v=.vo)
STD_GLOBFILES=$(STD_VFILES:.v=.glob)
STD_DEPFILES=$(STD_VFILES:.v=.d)
STD_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).coq.theories.%,$(srcdir)/html/Coq.%,$(subst /,.,$(STD_VFILES:.v=.html)))
STD_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(STD_HTMLFILES))
STD_DPDFILES=$(patsubst $(subst /,.,$(srcdir)).coq.theories.%,$(srcdir)/file-dep-graphs/Coq.%,$(subst /,.,$(STD_VFILES:.v=.dpd)))

# The list of all files, mainly used for html and proviola
MAIN_VFILES = $(CORE_VFILES) $(CATEGORY_VFILES) $(CONTRIB_VFILES)
MAIN_VOFILES = $(MAIN_VFILES:.v=.vo)
MAIN_GLOBFILES = $(MAIN_VFILES:.v=.glob)
MAIN_DEPFILES = $(MAIN_VFILES:.v=.d)
MAIN_HTMLFILES = $(CORE_HTMLFILES) $(CATEGORY_HTMLFILES) $(CONTRIB_HTMLFILES)
MAIN_TIMING_HTMLFILES = $(CORE_TIMING_HTMLFILES) $(CATEGORY_TIMING_HTMLFILES) $(CONTRIB_TIMING_HTMLFILES)
MAIN_DPDFILES = $(CORE_DPDFILES) $(CATEGORY_DPDFILES)

ALL_VFILES = $(STD_VFILES) $(MAIN_VFILES)
ALL_VOFILES = $(STD_VOFILES) $(MAIN_VOFILES)
ALL_GLOBFILES=$(STD_GLOBFILES) $(MAIN_GLOBFILES)
ALL_DEPFILES=$(STD_DEPFILES) $(MAIN_DEPFILES)
ALL_HTMLFILES=$(STD_HTMLFILES) $(MAIN_HTMLFILES)
ALL_TIMING_HTMLFILES=$(STD_TIMING_HTMLFILES) $(MAIN_TIMING_HTMLFILES)
ALL_TIMINGFILES=$(ALL_VFILES:.v=.timing)
ALL_XMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/proviola-xml/%,$(ALL_HTMLFILES:.html=.xml))
ALL_PROVIOLA_HTMLFILES=$(patsubst $(srcdir)/proviola-xml/%,$(srcdir)/proviola-html/%,$(ALL_XMLFILES:.xml=.html))
ALL_DPDFILES=$(MAIN_DPDFILES) # $(STD_DPDFILES)
ALL_SVGFILES=$(ALL_DPDFILES:.dpd=.svg)
ALL_DOTFILES=$(ALL_DPDFILES:.dpd=.dot)

# Definitions that let autoconf know how to install things.
nobase_hott_DATA = \
	$(STD_VOFILES) \
	$(CORE_VOFILES) \
	$(CATEGORY_VOFILES) \
	$(CONTRIB_VOFILES) \
	$(shell find "$(SRCCOQLIB)/theories" -name "README.txt")

# The Coq compiler, adapted to HoTT
HOQC=$(srcdir)/hoqc

# Which files should be cleaned
CLEANFILES = $(ALL_VOFILES) $(ALL_GLOBFILES) $(ALL_DEPFILES) $(ALL_HTMLFILES) $(ALL_XMLFILES) $(ALL_PROVIOLA_HTMLFILES) $(ALL_TIMINGFILES) $(ALL_TIMING_HTMLFILES) html-done.timestamp HoTT.deps HoTTCore.deps $(ALL_SVGFILES) $(ALL_DPDFILES) $(ALL_DOTFILES) file-dep-graphs/hott-all.dot file-dep-graphs/hott-all.dpd file-dep-graphs/hott-all.svg file-dep-graphs/hott-lib.dot file-dep-graphs/hott-lib.dpd file-dep-graphs/hott-lib.svg

# automake is very stupid and wants to put the 'include' line above
# after this target.  But this target depends on variables defined in
# that file, so we explicitly put the target here to trick automake
# into putting the include in the right place.
all-am: Makefile $(SCRIPTS) $(DATA) $(MAKEFILE_TARGETS_FILE)

.SECONDEXPANSION:

.PHONY: stdlib hottlib hott-core hott-categories contrib clean html proviola timing-html clean-local install-data-local proviola-all proviola-xml svg-file-dep-graphs svg-aggregate-dep-graphs svg-dep-graphs clean-dpdgraph

# TODO(JasonGross): Get this to work on Windows, where symlinks are unreliable
install-data-local:
	$(MKDIR_P) "$(hottdir)/coq"
	rm -f "$(hottdir)/coq/dev" "$(hottdir)/coq/plugins"
	$(LN_S) "$(COQLIB)/dev" "$(hottdir)/coq"
	$(LN_S) "$(COQLIB)/plugins" "$(hottdir)/coq"

# The standard library files must be compiled in a special way
stdlib: $(STD_VOFILES)

$(STD_VOFILES) : %.vo : %.v
	$(VECHO) COQTOP $*
	$(Q) $(TIMER) etc/pipe_out.sh "$*.timing" "$(COQTOP)" -time -indices-matter -boot -nois -no-native-compiler -coqlib "$(SRCCOQLIB)" -R "$(SRCCOQLIB)/theories" Coq -compile "$*"


# The HoTT library as a single target
hott-core: $(CORE_VOFILES)

hott-categories: $(CATEGORY_VOFILES)

contrib: $(CONTRIB_VOFILES)

hottlib: hott-core hott-categories contrib

# a strict rule that will error if there are .v files around which aren't in Makefile_targets.mk
strict-test:
	$(Q) if [ x"$(UNBUILT_VFILES)" != x ]; then \
	    echo "Error: The files '$(UNBUILT_VFILES)' are present but are not in $(MAKEFILE_TARGETS_FILE)"; \
	    exit 1; \
	fi

strict: strict-test hottlib hott-core hott-categories contrib

# A rule for compiling the HoTT libary files
$(MAIN_VOFILES) : %.vo : %.v $(STD_VOFILES)
	$(VECHO) HOQC $*
	$(Q) $(TIMER) ./etc/pipe_out.sh "$*.timing" $(HOQC) -time $<

# The deps file, for graphs
HoTT.deps: $(ALL_VFILES)
	$(VECHO) COQDEP > $@
	$(Q) "$(COQDEP)" -nois -coqlib "$(SRCCOQLIB)" -R "$(srcdir)/theories" HoTT -R "$(SRCCOQLIB)/theories" Coq $(ALL_VFILES) | sed s'#\\#/#g' >$@

HoTTCore.deps: $(CORE_VFILES)
	$(VECHO) COQDEP > $@
	$(Q) "$(COQDEP)" -nois -coqlib "$(SRCCOQLIB)" -R "$(srcdir)/theories" HoTT -R "$(SRCCOQLIB)/theories" Coq $(CORE_VFILES) | sed s'#\\#/#g' >$@

# The HTML files
# We have a dummy file, to allow us to depend on the html files without
# remaking them every time, and to prevent make -j2 from running coqdoc
# twice.
html-done.timestamp: $(ALL_GLOBFILES) $(ALL_VFILES)
	- $(mkdir_p) html
	touch html-done.timestamp
	"$(COQDOC)" -toc -interpolate -utf8 -html --coqlib_path "$(SRCCOQLIB)" --no-externals -R "$(srcdir)/theories" HoTT -R "$(SRCCOQLIB)/theories" Coq -d html $(ALL_VFILES)

html:
	rm -f html-done.timestamp
	$(MAKE) html-done.timestamp

timing-html: $(ALL_TIMING_HTMLFILES) timing-html/coqdoc.css timing-html/toc.html

timing-html/coqdoc.css timing-html/toc.html: timing-html/% : html/%
	@ $(mkdir_p) timing-html
	cp "$<" "$@"

$(ALL_HTMLFILES) html/index.html html/coqdoc.css html/toc.html : html-done.timestamp

$(CORE_TIMING_HTMLFILES) $(CATEGORY_TIMING_HTMLFILES): timing-html/HoTT.%.html : theories/$$(subst .,/,$$*).vo etc/time2html
	@ $(mkdir_p) $(dir $@)
	$(VECHO) TIME2HTML HoTT.$* > $@
	$(Q) etc/time2html "$(<:.vo=.timing)" "$(<:.vo=.v)" > $@

$(CONTRIB_TIMING_HTMLFILES): timing-html/%.html : contrib/$$(subst .,/,$$*).vo etc/time2html
	@ $(mkdir_p) $(dir $@)
	$(VECHO) TIME2HTML $* > $@
	$(Q) etc/time2html "$(<:.vo=.timing)" "$(<:.vo=.v)" > $@

$(STD_TIMING_HTMLFILES): timing-html/Coq.%.html : coq/theories/$$(subst .,/,$$*).vo etc/time2html
	@ $(mkdir_p) $(dir $@)
	$(VECHO) TIME2HTML Coq.$* > $@
	$(Q) etc/time2html "$(<:.vo=.timing)" "$(<:.vo=.v)" > $@



# the proviola files
proviola-html/index.html proviola-html/toc.html proviola-html/coqdoc.css : proviola-html/% : html/%
	- $(mkdir_p) proviola-html
	cp -f $< $@

proviola-html/proviola.css : proviola-html/% : proviola/proviola/ppcoqdoc/%
	- $(mkdir_p) proviola-html
	cp -f $< $@

proviola-xml/proviola.css proviola-xml/proviola.xsl : proviola-xml/% : proviola/proviola/ppcoqdoc/%
	- $(mkdir_p) proviola-xml
	cp -f $< $@

proviola-xml/%.xml: html/%.html
	@$(mkdir_p) proviola-xml
	$(VECHO) CAMERA $<
	$(Q) $(CAMERA) --coqtop "$(srcdir)/hoqtop" $< $@

proviola-html/%.html: proviola-xml/%.xml proviola-xml/proviola.xsl
	@$(mkdir_p) proviola-html
	$(VECHO) XSLTPROC $<
	$(Q) xsltproc $< > $@

proviola: $(ALL_PROVIOLA_HTMLFILES) proviola-html/proviola.css proviola-html/toc.html proviola-html/coqdoc.css proviola-html/index.html

proviola-xml: $(ALL_XMLFILES)

proviola-all: proviola proviola-xml

# dpdgraphs
etc/dpdgraph-0.4alpha/coqthmdep: etc/dpdgraph-0.4alpha/searchdepend.ml4 etc/dpdgraph-0.4alpha/graphdepend.ml4
	$(VECHO) MAKE DPDGRAPH
	$(Q) cd etc/dpdgraph-0.4alpha && $(MAKE)

%.svg: %.dot
	$(VECHO) DOT $< -o $@
	$(Q) if [ -s "$<" ]; then dot -Tsvg "$<" -o "$@"; else (echo "" > "$@"; touch "$@"); fi # don't do anything if zero size

file-dep-graphs/%.dot: file-dep-graphs/%.dpd etc/dpdgraph-0.4alpha/coqthmdep
	$(VECHO) DPD2DOT $< -o $@
	$(Q) if [ -s "$<" ]; then etc/dpdgraph-0.4alpha/dpd2dot $< -graphname $(subst -,_,$(subst .,_,$*)) -o $@ >/dev/null; else (echo "" > "$@"; touch "$@"); fi

$(MAIN_DPDFILES): file-dep-graphs/HoTT.%.dpd : theories/$$(subst .,/,$$*).vo etc/dpdgraph-0.4alpha/coqthmdep
	@ $(mkdir_p) $(dir $@)
	$(VECHO) HOQTHMDEP HoTT.$* > $@
	$(Q) (echo "Require HoTT.$*."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph HoTT.$*.') | etc/dpdgraph-0.4alpha/hoqthmdep 2>/dev/null >/dev/null

$(STD_DPDFILES): file-dep-graphs/Coq.%.dpd : coq/theories/$$(subst .,/,$$*).vo etc/dpdgraph-0.4alpha/coqthmdep
	@ $(mkdir_p) $(dir $@)
	$(VECHO) HOQTHMDEP Coq.$* > $@
	$(Q) (echo "Require Coq.$*."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph Coq.$*.') | etc/dpdgraph-0.4alpha/hoqthmdep 2>/dev/null >/dev/null

file-dep-graphs/hott-lib.dpd: etc/dpdgraph-0.4alpha/coqthmdep $(CORE_VOFILES)
	@ $(mkdir_p) $(dir $@)
	$(VECHO) HOQTHMDEP HoTTLib
        HOTT_LIB_FILES=$(subst /,.,$(patsubst $(srcdir)/theories/%.v,HoTT.%,$(CORE_VFILES)))
	$(Q) (echo "Require $(HOTT_LIB_FILES)."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph $(HOTT_LIB_FILES).') | etc/dpdgraph-0.4alpha/hoqthmdep 2>/dev/null >/dev/null

#file-dep-graphs/hott-all.dpd: etc/dpdgraph-0.4alpha/coqthmdep $(CORE_VOFILES) $(CATEGORY_VOFILES)
#	@ $(mkdir_p) $(dir $@)
#	$(VECHO) HOQTHMDEP HoTT
#        HOTT_ALL_FILES=$(subst /,.,$(patsubst $(srcdir)/theories/%.v,HoTT.%,$(CORE_VFILES) $(CATEGORY_VFILES)))
#	$(Q) (echo "Require $(HOTT_ALL_FILES)."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph $(HOTT_ALL_FILES).') | etc/dpdgraph-0.4alpha/hoqthmdep 2>/dev/null >/dev/null

file-dep-graphs/index.html: Makefile_targets.mk
	@ $(mkdir_p) $(dir $@)
	$(VECHO) MAKE $@
	$(Q) (echo "<html><head><title>Dependency Graphs</title></head><body>"; \
		echo '<ul><!--li><a href="hott-all.svg">Entire HoTT Library</a></li-->'; \
		echo '<li><a href="hott-lib.svg">HoTT Core Library</a></li>'; \
		for i in $(patsubst $(srcdir)/file-dep-graphs/%.svg,%,$(ALL_SVGFILES)); \
		do echo "<li><a href=\"$$i.svg\">$$i</a></li>"; \
		done; \
		echo "</ul></body></html>") \
		> $@

svg-dep-graphs: svg-file-dep-graphs svg-aggregate-dep-graphs

dot-dep-graphs: dot-file-dep-graphs dot-aggregate-dep-graphs

svg-aggregate-dep-graphs: file-dep-graphs/hott-lib.svg #file-dep-graphs/hott-all.svg

dot-aggregate-dep-graphs: file-dep-graphs/hott-lib.dot #file-dep-graphs/hott-all.dot

svg-file-dep-graphs: $(ALL_SVGFILES) $(ALL_DOTFILES)

dot-file-dep-graphs: $(ALL_DOTFILES)

# The TAGS file
TAGS_FILES = $(ALL_VFILES)
TAGS : $(TAGS_FILES)
	$(ETAGS) --language=none \
	-r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Proposition\)[[:space:]]+\([[:alnum:]_'\'']+\)/\2/' \
	-r '/^[[:space:]]*\([[:alnum:]_'\'']+\)[[:space:]]*:/\1/' \
	$^

# Dependency files
$(ALL_DEPFILES) : %.d : %.v
	$(VECHO) COQDEP $<
	$(Q) "$(COQDEP)" -nois -coqlib "$(SRCCOQLIB)" -R "$(srcdir)/theories" HoTT -R "$(SRCCOQLIB)/theories" Coq $< | sed s'#\\#/#g' >$@

clean-dpdgraph:
	(cd etc/dpdgraph-0.4alpha && $(MAKE) clean)

clean:
	rm -f $(CLEANFILES)
	find "$(SRCCOQLIB)/theories" $(srcdir)/theories -name \*.vo -o -name \*.glob -o -name \*.timing | xargs rm -f

-include $(ALL_DEPFILES)
