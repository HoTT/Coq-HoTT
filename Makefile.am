ACLOCAL_AMFLAGS = -I etc

bin_SCRIPTS = hoqtop hoqc hoq-config
if make_hoqide
  bin_SCRIPTS += hoqide
endif
if make_hoqtopbyte
  bin_SCRIPTS += hoqtop.byte
endif

hottdir=$(datarootdir)/hott
EXTRA_DIST = coq theories ssrplugin etc LICENSE.txt CREDITS.txt INSTALL.txt README.markdown

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
# CATEGORY_VFILES.  To add more targets (e.g., SSR_VFILES), you'll
# need to update Makefile.am and run autogen.sh and configure again

MAKEFILE_TARGETS_FILE = Makefile_targets.mk

include $(MAKEFILE_TARGETS_FILE)

# The list of files that comprise the HoTT library
CORE_VOFILES=$(CORE_VFILES:.v=.vo)
CORE_GLOBFILES=$(CORE_VFILES:.v=.glob)
CORE_DEPFILES=$(CORE_VFILES:.v=.d)
CORE_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html/HoTT.%,$(subst /,.,$(CORE_VFILES:.v=.html)))

# The list of files that comprise the category theory in the HoTT library
CATEGORY_VOFILES=$(CATEGORY_VFILES:.v=.vo)
CATEGORY_GLOBFILES=$(CATEGORY_VFILES:.v=.glob)
CATEGORY_DEPFILES=$(CATEGORY_VFILES:.v=.d)
CATEGORY_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html/HoTT.%,$(subst /,.,$(CATEGORY_VFILES:.v=.html)))

# The list of files from contrib
CONTRIB_VOFILES=$(CONTRIB_VFILES:.v=.vo)
CONTRIB_GLOBFILES=$(CONTRIB_VFILES:.v=.glob)
CONTRIB_DEPFILES=$(CONTRIB_VFILES:.v=.d)
CONTRIB_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).contrib.%,$(srcdir)/html/%,$(subst /,.,$(CONTRIB_VFILES:.v=.html)))

# I'm not sure why we needs = rather than :=, but we seem to
ALL_BUILT_HOTT_VFILES = $(STD_VFILES) $(CORE_VFILES) $(CATEGORY_VFILES)
ALL_HOTT_VFILES = $(shell find "$(srcdir)/theories" -name "*.v") $(shell find "$(SRCCOQLIB)/theories" -name "*.v")
UNBUILT_VFILES = $(filter-out $(ALL_BUILT_HOTT_VFILES),$(ALL_HOTT_VFILES))

# The list of files that comprise the alternative standard library
STD_VOFILES=$(STD_VFILES:.v=.vo)
STD_GLOBFILES=$(STD_VFILES:.v=.glob)
STD_DEPFILES=$(STD_VFILES:.v=.d)
STD_HTMLFILES=$(patsubst $(subst /,.,$(srcdir)).coq.theories.%,$(srcdir)/html/Coq.%,$(subst /,.,$(STD_VFILES:.v=.html)))

if make_ssreflect
# The list of Coq files that comprise ssreflect
SSR_MAKEFILE=$(srcdir)/Makefile_ssrplugin
ssrdir=$(srcdir)/ssrplugin
SSR_VFILES=$(shell find "$(ssrdir)/theories" -name "*.v")
SSR_VOFILES=$(SSR_VFILES:.v=.vo)
SSR_GLOBFILES=$(SSR_VFILES:.v=.glob)
SSR_HTMLFILES=$(SSR_VFILES:.v=.html)
SSR_MLIFILES=$(shell find "$(ssrdir)/src" -name "*.mli")
SSR_MLFILES=$(shell find "$(ssrdir)/src" -name "*.ml4" -o -name "*.ml")
SSR_MLLIBFILES=$(shell find "$(ssrdir)/theories" -name "*.mllib")
SSR_CMXSFILES=$(SSR_MLLIBFILES:.mllib=.cmxs)
SSR_CMAFILES=$(SSR_MLLIBFILES:.mllib=.cma)
endif

# The list of all files, mainly used for html and proviola
MAIN_VFILES = $(CORE_VFILES) $(CATEGORY_VFILES) $(CONTRIB_VFILES)
MAIN_VOFILES = $(MAIN_VFILES:.v=.vo)
MAIN_GLOBFILES = $(MAIN_VFILES:.v=.glob)
MAIN_DEPFILES = $(MAIN_VFILES:.v=.d)
MAIN_HTMLFILES = $(CORE_HTMLFILES) $(CATEGORY_HTMLFILES) $(CONTRIB_HTMLFILES)

ALL_VFILES = $(STD_VFILES) $(MAIN_VFILES)
ALL_VOFILES = $(STD_VOFILES) $(MAIN_VOFILES)
ALL_GLOBFILES=$(STD_GLOBFILES) $(MAIN_GLOBFILES)
ALL_DEPFILES=$(STD_DEPFILES) $(MAIN_DEPFILES)
ALL_HTMLFILES=$(STD_HTMLFILES) $(MAIN_HTMLFILES)
ALL_XMLFILES=$(patsubst $(srcdir)/html/%,$(srcdir)/proviola-xml/%,$(ALL_HTMLFILES:.html=.xml))
ALL_PROVIOLA_HTMLFILES=$(patsubst $(srcdir)/proviola-xml/%,$(srcdir)/proviola-html/%,$(ALL_XMLFILES:.xml=.html))

# Definitions that let autoconf know how to install things.
nobase_hott_DATA = \
	$(STD_VOFILES) \
	$(CORE_VOFILES) \
	$(CATEGORY_VOFILES) \
	$(CONTRIB_VOFILES) \
	$(shell find "$(SRCCOQLIB)/theories" -name "README.txt") \
	$(SSR_VOFILES) \
	$(SSR_CMXSFILES) \
	$(SSR_CMAFILES)

# The Coq compiler, adapted to HoTT
HOQC=$(srcdir)/hoqc

# Which files should be cleaned
CLEANFILES = $(ALL_VOFILES) $(ALL_GLOBFILES) $(ALL_DEPFILES) $(ALL_HTMLFILES) $(ALL_XMLFILES) $(ALL_PROVIOLA_HTMLFILES) html-done.timestamp

# automake is very stupid and wants to put the 'include' line above
# after this target.  But this target depends on variables defined in
# that file, so we explicitly put the target here to trick automake
# into putting the include in the right place.
all-am: Makefile $(SCRIPTS) $(DATA) $(MAKEFILE_TARGETS_FILE)

if make_ssreflect
.PHONY: stdlib hottlib hott-core hott-categories contrib clean html proviola clean-local install-data-local proviola-all proviola-xml ssrplugin
else
.PHONY: stdlib hottlib hott-core hott-categories contrib clean html proviola clean-local install-data-local proviola-all proviola-xml
endif

# TODO(JasonGross): Get this to work on Windows, where symlinks are unreliable
install-data-local:
	$(MKDIR_P) "$(hottdir)/coq"
	rm -f "$(hottdir)/coq/dev" "$(hottdir)/coq/plugins"
	$(LN_S) "$(COQLIB)/dev" "$(hottdir)/coq"
	$(LN_S) "$(COQLIB)/plugins" "$(hottdir)/coq"

if make_ssreflect
clean-local: $(SSR_MAKEFILE)
	$(MAKE) -f "$(SSR_MAKEFILE)" COQBIN="$(COQBIN)/" clean
	rm -f "$(SSR_MAKEFILE)"
endif

# The standard library files must be compiled in a special way
stdlib: $(STD_VOFILES)

$(STD_VOFILES) : %.vo : %.v
	$(VECHO) COQTOP $(basename $<)
	$(Q) $(TIMER) "$(COQTOP)" -indices-matter -boot -nois -coqlib "$(SRCCOQLIB)" -R "$(SRCCOQLIB)/theories" Coq -compile "$(basename $<)"


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
if make_ssreflect
$(MAIN_VOFILES) : %.vo : %.v $(STD_VOFILES) $(SSR_VOFILES)
	$(VECHO) HOQC $<
	$(Q) $(TIMER) $(HOQC) $<
else
$(MAIN_VOFILES) : %.vo : %.v $(STD_VOFILES)
	$(VECHO) HOQC $<
	$(Q) $(TIMER) $(HOQC) $<
endif

if make_ssreflect
# Compilation of ssreflect is a bit more roundabout because ssreflect relies on coq_makefile,
# which we do not. Perhaps we should. Anyhow, we circumvent the "standard" ssreflect procedure
# to keep track of dependencies and what should be installed where. This will break if ssreflect
# changes its compilation procedure drastically.
ssrplugin: stdlib $(SSR_VOFILES)

$(SSR_MAKEFILE): $(ssrdir)/Make
	$(COQMAKEFILE) COQC = "$(SILENCE_HOQC)\$$(TIMER) \"$(HOQC)\"" COQDEP = "$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f "$(ssrdir)/Make" > "$(SSR_MAKEFILE)"

$(SSR_VOFILES): $(SSR_MAKEFILE) $(SSR_CMXSFILES) $(SSR_CMAFILES)

$(SSR_VOFILES) : %.vo : %.v
	$(MAKE) -f "$(SSR_MAKEFILE)" COQBIN="$(COQBIN)/" $@

$(SSR_CMXSFILES): $(SSR_MAKEFILE)

$(SSR_CMAFILES): $(SSR_MAKEFILE)

$(SSR_CMXSFILES): %.cmxs : %.mllib
	$(MAKE) -f "$(SSR_MAKEFILE)" COQBIN="$(COQBIN)/" $@

$(SSR_CMAFILES): %.cma : %.mllib
	$(MAKE) -f "$(SSR_MAKEFILE)" COQBIN="$(COQBIN)/" $@
endif

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


$(ALL_HTMLFILES) html/index.html html/coqdoc.css html/toc.html : html-done.timestamp


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

clean:
	rm -f $(CLEANFILES)
	find "$(SRCCOQLIB)/theories" $(srcdir)/theories -name \*.vo -o -name \*.glob | xargs rm -f

-include $(ALL_DEPFILES)
