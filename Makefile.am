ACLOCAL_AMFLAGS = -I etc

bin_SCRIPTS = hoqtop hoqc hoqdep hoq-config
if make_hoqide
  bin_SCRIPTS += hoqide
endif
if make_hoqtopbyte
  bin_SCRIPTS += hoqtop.byte
endif
if make_hoqchk
  bin_SCRIPTS += hoqchk
endif

hottdir=$(datarootdir)/hott
EXTRA_DIST = coq theories etc LICENSE.txt CREDITS.txt INSTALL.txt README.markdown

# The path to the Coq library in $(srcdir)
SRCCOQLIB=$(srcdir)/coq

# Extra standard library replacements to install
STDLIB_EXTRA_DIST = $(shell find -P $(addprefix "$(SRCCOQLIB)/",$(STDLIB_REPLACEMENT_DIRS)) -type f)

# Flags for hoqchk
HOQCHKFLAGS=-silent -o

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

# inner vecho, without the @
VIECHO_0 := echo
VIECHO_1 := true
VIECHO = $(VIECHO_$(V))

SILENCE_HOQC_0 := @echo \"HOQC $$<\"; #
SILENCE_HOQC_1 :=
SILENCE_HOQC = $(SILENCE_HOQC_$(V))

SILENCE_COQDEP_0 := @echo \"COQDEP $$<\"; #
SILENCE_COQDEP_1 :=
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

# the proviola camera
CAMERA = python proviola/camera/camera.py

# read the targets from _CoqMakefile, except for STD_VFILES

STD_VFILES = \
	$(SRCCOQLIB)/theories/Init/Notations.v \
	$(SRCCOQLIB)/theories/Init/Logic.v \
	$(SRCCOQLIB)/theories/Init/Datatypes.v \
	$(SRCCOQLIB)/theories/Init/Logic_Type.v \
	$(SRCCOQLIB)/theories/Init/Peano.v \
	$(SRCCOQLIB)/theories/Init/Tactics.v \
	$(SRCCOQLIB)/theories/Init/Specif.v \
	$(SRCCOQLIB)/theories/Init/Decimal.v \
	$(SRCCOQLIB)/theories/Init/Nat.v \
	$(SRCCOQLIB)/theories/Init/Prelude.v \
	$(SRCCOQLIB)/theories/Bool/Bool.v \
	$(SRCCOQLIB)/theories/Unicode/Utf8_core.v \
	$(SRCCOQLIB)/theories/Unicode/Utf8.v \
	$(SRCCOQLIB)/theories/Program/Tactics.v

COQ_PROJECT_CONTENTS = $(shell cat $(srcdir)/_CoqProject)

CATEGORY_VFILES = $(addprefix $(srcdir)/,$(filter theories/Categories%.v, $(COQ_PROJECT_CONTENTS)))
CORE_VFILES = $(filter-out $(CATEGORY_VFILES),$(addprefix $(srcdir)/,$(filter theories/%.v, $(COQ_PROJECT_CONTENTS))))
CONTRIB_VFILES = $(addprefix $(srcdir)/,$(filter contrib/%.v, $(COQ_PROJECT_CONTENTS)))

# The list of files that comprise the HoTT library
VO=vo
CORE_VOFILES=$(CORE_VFILES:.v=.$(VO))
CORE_GLOBFILES=$(CORE_VFILES:.v=.glob)
CORE_DEPFILES=$(CORE_VFILES:.v=.v.d)
CORE_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html/HoTT.%,$(subst /,.,$(CORE_VFILES:.v=.html)))
CORE_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(CORE_HTMLFILES))
CORE_DPDFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/file-dep-graphs/HoTT.%,$(subst /,.,$(CORE_VFILES:.v=.dpd)))

# The list of files that comprise the category theory in the HoTT library
CATEGORY_VOFILES=$(CATEGORY_VFILES:.v=.$(VO))
CATEGORY_GLOBFILES=$(CATEGORY_VFILES:.v=.glob)
CATEGORY_DEPFILES=$(CATEGORY_VFILES:.v=.v.d)
CATEGORY_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html/HoTT.%,$(subst /,.,$(CATEGORY_VFILES:.v=.html)))
CATEGORY_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(CATEGORY_HTMLFILES))
CATEGORY_DPDFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/file-dep-graphs/HoTT.%,$(subst /,.,$(CATEGORY_VFILES:.v=.dpd)))

# The list of files from contrib
CONTRIB_VOFILES=$(CONTRIB_VFILES:.v=.$(VO))
CONTRIB_GLOBFILES=$(CONTRIB_VFILES:.v=.glob)
CONTRIB_DEPFILES=$(CONTRIB_VFILES:.v=.v.d)
CONTRIB_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).contrib.%,$(srcdir)/html/%,$(subst /,.,$(CONTRIB_VFILES:.v=.html)))
CONTRIB_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(CONTRIB_HTMLFILES))

# I'm not sure why we needs = rather than :=, but we seem to
ALL_BUILT_HOTT_VFILES = $(STD_VFILES) $(CORE_VFILES) $(CATEGORY_VFILES)
ALL_HOTT_VFILES = $(shell find "$(srcdir)/theories" -name "*.v") $(shell find "$(SRCCOQLIB)/theories" -name "*.v")
UNBUILT_VFILES = $(filter-out $(ALL_BUILT_HOTT_VFILES),$(ALL_HOTT_VFILES))

# The list of files that comprise the alternative standard library
# the .vi infrastructure doesn't work unless we have .vos for the
# standard library
STD_VOFILES=$(STD_VFILES:.v=.vo)
STD_GLOBFILES=$(STD_VFILES:.v=.glob)
STD_DEPFILES=$(STD_VFILES:.v=.v.d)
STD_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).coq.theories.%,$(srcdir)/html/Coq.%,$(subst /,.,$(STD_VFILES:.v=.html)))
STD_TIMING_HTMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/timing-html/%,$(STD_HTMLFILES))
STD_DPDFILES=$(patsubst $(subst /,.,$(srcdir)).coq.theories.%,$(srcdir)/file-dep-graphs/Coq.%,$(subst /,.,$(STD_VFILES:.v=.dpd)))

# The list of all files, mainly used for html and proviola
MAIN_VFILES = $(CORE_VFILES) $(CATEGORY_VFILES) $(CONTRIB_VFILES)
MAIN_VOFILES = $(MAIN_VFILES:.v=.$(VO))
MAIN_GLOBFILES = $(MAIN_VFILES:.v=.glob)
MAIN_DEPFILES = $(MAIN_VFILES:.v=.v.d)
MAIN_HTMLFILES = $(CORE_HTMLFILES) $(CATEGORY_HTMLFILES) $(CONTRIB_HTMLFILES)
MAIN_TIMING_HTMLFILES = $(CORE_TIMING_HTMLFILES) $(CATEGORY_TIMING_HTMLFILES) $(CONTRIB_TIMING_HTMLFILES)
MAIN_DPDFILES = $(CORE_DPDFILES) $(CATEGORY_DPDFILES)

ALL_VFILES = $(STD_VFILES) $(MAIN_VFILES)
ALL_VOFILES = $(STD_VOFILES) $(MAIN_VOFILES)
ALL_GLOBFILES=$(STD_GLOBFILES) $(MAIN_GLOBFILES)
ALL_DEPFILES=$(STD_DEPFILES) $(MAIN_DEPFILES)
ALL_HTMLFILES=$(STD_HTMLFILES) $(MAIN_HTMLFILES)
ALL_TIMING_HTMLFILES=$(STD_TIMING_HTMLFILES) $(MAIN_TIMING_HTMLFILES)
ALL_TIMINGFILES=$(ALL_VFILES:.v=.v.timing)
ALL_XMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/proviola-xml/%,$(ALL_HTMLFILES:.html=.xml))
ALL_PROVIOLA_HTMLFILES=$(patsubst $(srcdir)/proviola-xml/%,$(srcdir)/proviola-html/%,$(ALL_XMLFILES:.xml=.html))
ALL_DPDFILES=$(MAIN_DPDFILES) # $(STD_DPDFILES)
ALL_SVGFILES=$(ALL_DPDFILES:.dpd=.svg)
ALL_DOTFILES=$(ALL_DPDFILES:.dpd=.dot)

# Definitions that let autoconf know how to install things.
nobase_hott_DATA = \
	$(ALL_VOFILES) \
	$(ALL_GLOBFILES) \
	$(STDLIB_EXTRA_DIST) \
	$(shell find "$(SRCCOQLIB)/theories" -name "README.txt")

# The Coq compiler, adapted to HoTT
HOQC=$(srcdir)/hoqc
HOQCHK=$(srcdir)/hoqchk

# Which extra files should be cleaned
EXTRA_CLEANFILES = html-done.timestamp HoTT.deps HoTTCore.deps file-dep-graphs/hott-all.dot file-dep-graphs/hott-all.dpd file-dep-graphs/hott-all.svg file-dep-graphs/hott-lib.dot file-dep-graphs/hott-lib.dpd file-dep-graphs/hott-lib.svg

# automake is very stupid and wants to put the 'include' line above
# after this target.  But this target depends on variables defined in
# that file, so we explicitly put the target here to trick automake
# into putting the include in the right place.
all-am: Makefile $(SCRIPTS) $(DATA) _CoqProject

.SECONDEXPANSION:

.PHONY: stdlib hottlib hott-core hott-categories contrib clean html proviola timing-html clean-local install-data-local proviola-all proviola-xml svg-file-dep-graphs svg-aggregate-dep-graphs svg-dep-graphs clean-dpdgraph strict strict-test strict-no-axiom quick vi2vo checkproofs validate

# targets that we don't need to run coqdep for
FAST_TARGETS = clean clean-local clean-dpdgraph TAGS

if install_stdlib_symlinks
install-data-local:
	$(MKDIR_P) "$(hottdir)/coq"
	$(Q)for i in $(STDLIB_REPLACEMENT_DIRS); do \
		$(VIECHO) "INSTALL coq/$$i"; \
		rm -f "$(hottdir)/coq/$$i"; \
		$(LN_S) "$(COQLIB)/$$i" "$(hottdir)/coq"; \
	done
endif

# The standard library files must be compiled in a special way
stdlib: $(STD_VOFILES)

quick:
	$(MAKE) all VO=vi

vi2vo:
	$(VECHO) HOQC -schedule-vi2vo
	$(Q) $(TIMER) $(HOQC) -schedule-vi2vo $(J) $(MAIN_VOFILES:%.vo=%.vi)

checkproofs:
	$(VECHO) HOQC -schedule-vi-checking
	$(Q) $(TIMER) $(HOQC) -schedule-vi-checking $(J) $(MAIN_VOFILES:%.vo=%.vi)

validate: $(ALL_VOFILES)
	$(VECHO) HOQCHK
	$(Q) $(TIMER) $(HOQCHK) $(HOQCHKFLAGS) $^

$(STD_VOFILES) : %.vo : %.v coq-HoTT
	$(VECHO) COQC $*
	$(Q) $(TIMER) etc/pipe_out.sh "$<.timing" "$(COQC)" -time -indices-matter -boot -nois -coqlib "$(SRCCOQLIB)" -R "$(SRCCOQLIB)/theories" Coq "$<"


# The HoTT library as a single target
hott-core: $(CORE_VOFILES)

hott-categories: $(CATEGORY_VOFILES)

contrib: $(CONTRIB_VOFILES)

hottlib: hott-core hott-categories contrib

# a strict rule that will error if there are .v files around which aren't in _CoqProject
strict-test:
	$(Q) if [ x"$(UNBUILT_VFILES)" != x ]; then \
	    echo "Error: The files '$(UNBUILT_VFILES)' are present but are not in _CoqProject"; \
	    exit 1; \
	fi

# a rule that will error if there are any .v files that require FunextAxiom or UnivalenceAxiom
strict-no-axiom: $(ALL_GLOBFILES)
	$(Q) if [ ! -z "$$(grep 'HoTT\.\(FunextAxiom\|UnivalenceAxiom\) <> <> lib' -l $<)" ]; then \
	    echo "Error: The files '$$(grep 'HoTT\.\(FunextAxiom\|UnivalenceAxiom\) <> <> lib' -l $<)' depend on FunextAxiom or UnivalenceAxiom."; \
	    exit 1; \
	fi

strict: strict-test strict-no-axiom hottlib hott-core hott-categories contrib

# A rule for compiling the HoTT libary files
$(MAIN_VFILES:.v=.vo) : %.vo : %.v $(STD_VOFILES) coq-HoTT
	$(VECHO) HOQC $*
	$(Q) $(TIMER) ./etc/pipe_out.sh "$<.timing" $(HOQC) -q -time $<

$(MAIN_VFILES:.v=.vi) : %.vi : %.v $(STD_VOFILES) coq-HoTT
	$(VECHO) HOQC -quick $*
	$(Q) $(TIMER) ./etc/pipe_out.sh "$<.timing" $(HOQC) -q -quick -time $<

# The deps file, for graphs
HoTT.deps: $(ALL_VFILES)
	$(VECHO) COQDEP > $@
	$(Q) "$(COQDEP)" -nois -coqlib "$(SRCCOQLIB)" -R "$(srcdir)/theories" HoTT -Q "$(srcdir)/contrib" "" -R "$(SRCCOQLIB)/theories" Coq $(ALL_VFILES) | sed s'#\\#/#g' >$@

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
	"$(COQDOC)" -toc -interpolate -utf8 -html --coqlib_path "$(SRCCOQLIB)" --no-externals -R "$(srcdir)/theories" HoTT -Q "$(srcdir)/contrib" "" -R "$(SRCCOQLIB)/theories" Coq -d html $(ALL_VFILES)

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
	$(Q) etc/time2html "$(<:.vo=.v.timing)" "$(<:.vo=.v)" > $@

$(CONTRIB_TIMING_HTMLFILES): timing-html/%.html : contrib/$$(subst .,/,$$*).vo etc/time2html
	@ $(mkdir_p) $(dir $@)
	$(VECHO) TIME2HTML $* > $@
	$(Q) etc/time2html "$(<:.vo=.v.timing)" "$(<:.vo=.v)" > $@

$(STD_TIMING_HTMLFILES): timing-html/Coq.%.html : coq/theories/$$(subst .,/,$$*).vo etc/time2html
	@ $(mkdir_p) $(dir $@)
	$(VECHO) TIME2HTML Coq.$* > $@
	$(Q) etc/time2html "$(<:.vo=.v.timing)" "$(<:.vo=.v)" > $@



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
COQTHMDEP=etc/coq-dpdgraph/coqthmdep
HOQTHMDEP=etc/hoqthmdep
$(COQTHMDEP): etc/coq-dpdgraph/searchdepend.mlg etc/coq-dpdgraph/graphdepend.mlg etc/coq-dpdgraph/Makefile
	$(VECHO) MAKE DPDGRAPH
	$(Q) cd etc/coq-dpdgraph && $(MAKE)

etc/coq-dpdgraph/Makefile: etc/coq-dpdgraph/Makefile.in etc/coq-dpdgraph/configure
	$(VECHO) "CD DPDGRAPH && ./configure"
	$(Q) cd etc/coq-dpdgraph && ./configure

etc/coq-dpdgraph/configure: etc/coq-dpdgraph/configure.ac
	$(VECHO) "CD DPDGRAPH && AUTORECONF"
	$(Q) cd etc/coq-dpdgraph && autoreconf -fvi

%.svg: %.dot
	$(VECHO) DOT $< -o $@
	$(Q) if [ -s "$<" ]; then dot -Tsvg "$<" -o "$@"; else (echo "" > "$@"; touch "$@"); fi # don't do anything if zero size

file-dep-graphs/%.dot: file-dep-graphs/%.dpd $(COQTHMDEP)
	$(VECHO) DPD2DOT $< -o $@
	$(Q) if [ -s "$<" ]; then etc/coq-dpdgraph/dpd2dot $< -graphname $(subst -,_,$(subst .,_,$*)) -o $@ >/dev/null; else (echo "" > "$@"; touch "$@"); fi

$(MAIN_DPDFILES): file-dep-graphs/HoTT.%.dpd : theories/$$(subst .,/,$$*).vo $(COQTHMDEP)
	@ $(mkdir_p) $(dir $@)
	$(VECHO) HOQTHMDEP HoTT.$* > $@
	$(Q) (echo "Require HoTT.$*."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph HoTT.$*.') | $(HOQTHMDEP) 2>/dev/null >/dev/null

$(STD_DPDFILES): file-dep-graphs/Coq.%.dpd : coq/theories/$$(subst .,/,$$*).vo $(COQTHMDEP)
	@ $(mkdir_p) $(dir $@)
	$(VECHO) HOQTHMDEP Coq.$* > $@
	$(Q) (echo "Require Coq.$*."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph Coq.$*.') | $(HOQTHMDEP) 2>/dev/null >/dev/null

file-dep-graphs/hott-lib.dpd: $(COQTHMDEP) $(CORE_VOFILES)
	@ $(mkdir_p) $(dir $@)
	$(VECHO) HOQTHMDEP HoTTLib
        HOTT_LIB_FILES=$(subst /,.,$(patsubst $(srcdir)/theories/%.v,HoTT.%,$(CORE_VFILES)))
	$(Q) (echo "Require $(HOTT_LIB_FILES)."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph $(HOTT_LIB_FILES).') | $(HOQTHMDEP) 2>/dev/null >/dev/null

#file-dep-graphs/hott-all.dpd: $(COQTHMDEP) $(CORE_VOFILES) $(CATEGORY_VOFILES)
#	@ $(mkdir_p) $(dir $@)
#	$(VECHO) HOQTHMDEP HoTT
#        HOTT_ALL_FILES=$(subst /,.,$(patsubst $(srcdir)/theories/%.v,HoTT.%,$(CORE_VFILES) $(CATEGORY_VFILES)))
#	$(Q) (echo "Require $(HOTT_ALL_FILES)."; echo 'Set DependGraph File "$@".'; echo 'Print FileDependGraph $(HOTT_ALL_FILES).') | $(HOQTHMDEP) 2>/dev/null >/dev/null

file-dep-graphs/index.html: Makefile _CoqProject
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
$(MAIN_DEPFILES) : %.v.d : %.v
	$(VECHO) COQDEP $<
	$(Q) "$(COQDEP)" -nois -coqlib "$(SRCCOQLIB)" -R "$(srcdir)/theories" HoTT -Q "$(srcdir)/contrib" "" -R "$(SRCCOQLIB)/theories" Coq $< | sed s'#\\#/#g' >$@

$(STD_DEPFILES) : %.v.d : %.v
	$(VECHO) COQDEP $<
	$(Q) "$(COQDEP)" -nois -coqlib "$(SRCCOQLIB)" -R "$(SRCCOQLIB)/theories" Coq $< | sed s'#\\#/#g' >$@

clean-dpdgraph::
	(cd etc/coq-dpdgraph && $(MAKE) clean)

# We separate things to work around `make: execvp: /bin/bash: Argument list too long`
clean::
	$(VECHO) "RM *.VO"
	$(Q)rm -f $(ALL_VOFILES)
	$(VECHO) "RM *.VIO"
	$(Q)rm -f $(ALL_VFILES:.v=.vio)
	$(VECHO) "RM *.GLOB"
	$(Q)rm -f $(ALL_GLOBFILES)
	$(VECHO) "RM *.V.D"
	$(Q)rm -f $(ALL_DEPFILES)
	$(VECHO) "RM *.HTML"
	$(Q)rm -f $(ALL_HTMLFILES)
	$(VECHO) "RM *.XML"
	$(Q)rm -f $(ALL_XMLFILES)
	$(VECHO) "RM *.HTML"
	$(Q)rm -f $(ALL_PROVIOLA_HTMLFILES)
	$(VECHO) "RM *.TIMING"
	$(Q)rm -f $(ALL_TIMINGFILES)
	$(VECHO) "RM *.TIMING.HTML"
	$(Q)rm -f $(ALL_TIMING_HTMLFILES)
	$(VECHO) "RM *.SVG"
	$(Q)rm -f $(ALL_SVGFILES)
	$(VECHO) "RM *.DPD"
	$(Q)rm -f $(ALL_DPDFILES)
	$(VECHO) "RM *.DOT"
	$(Q)rm -f $(ALL_DOTFILES)
	rm -f $(EXTRA_CLEANFILES)
	find "$(SRCCOQLIB)/theories" $(srcdir)/theories -name \*.vo -o -name \*.glob -o -name \*.timing | xargs rm -f

@include_snippet@
