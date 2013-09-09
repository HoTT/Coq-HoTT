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

if BUNDLE_COQ
# The path to the local Coq distribution in $(builddir)
SRCCOQDIR=$(abs_srcdir)/coq-HoTT
BUILDCOQDIR=$(abs_builddir)/coq-HoTT
endif

# support the TIMED variable like coq_makefile
TIMED=
TIMECMD=
#STDTIME=@STDTIME@
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

# The list of files that comprise the HoTT library
VFILES=$(shell find $(srcdir)/theories -name "*.v")
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
DEPFILES:=$(VFILES:.v=.d)
HTMLFILES:=$(VFILES:.v=.html)

# The list of files that comprise the alternative standard library
STDVFILES=$(shell find $(SRCCOQLIB) -name "*.v")
STDVOFILES:=$(STDVFILES:.v=.vo)
STDGLOBFILES:=$(STDVFILES:.v=.glob)
STDDEPFILES:=$(STDVFILES:.v=.d)
STDHTMLFILES:=$(STDVFILES:.v=.html)

if make_ssreflect
# The list of Coq files that comprise ssreflect
SSRMAKEFILE=$(srcdir)/Makefile_ssrplugin
ssrdir=$(srcdir)/ssrplugin
SSRVFILES=$(shell find $(ssrdir)/theories -name "*.v")
SSRVOFILES=$(SSRVFILES:.v=.vo)
SSRGLOBFILES=$(SSRVFILES:.v=.glob)
SSRHTMLFILES:=$(SSRVFILES:.v=.html)
SSRMLIFILES=$(shell find $(ssrdir)/src -name "*.mli")
SSRMLFILES=$(shell find $(ssrdir)/src -name "*.ml4" -o -name "*.ml")
SSRMLLIBFILES=$(shell find $(ssrdir)/theories -name "*.mllib")
SSRCMXSFILES=$(SSRMLLIBFILES:.mllib=.cmxs)
SSRCMAFILES=$(SSRMLLIBFILES:.mllib=.cma)
endif

# Definitions that let autoconf know how to install things.
nobase_hott_DATA = \
	$(VOFILES) \
	$(STDVOFILES) \
	$(shell find $(SRCCOQLIB)/theories -name "README.txt") \
	$(SSRVOFILES) \
	$(SSRCMXSFILES) \
	$(SSRCMAFILES)

# The Coq compiler, adapted to HoTT
HOQC=$(srcdir)/hoqc

# Which files should be cleaned
CLEANFILES = $(VOFILES) $(GLOBFILES) $(STDVOFILES) $(STDGLOBFILES) $(DEPFILES) $(STDDEPFILES) $(HTMLFILES) $(STDHTMLFILES)

if make_ssreflect
.PHONY: stdlib hottlib ssrplugin coqlight
else
.PHONY: stdlib hottlib coqlight
endif

if BUNDLE_COQ
COQLIGHT_DEP = coqlight
else
COQLIGHT_DEP =
endif

$(LOCAL_COQC): $(COQLIGHT_DEP)

$(LOCAL_COQDEP): $(COQLIGHT_DEP)

$(LOCAL_COQDOC): $(COQLIGHT_DEP)

$(LOCAL_COQMAKEFILE): $(COQLIGHT_DEP)

$(LOCAL_COQTOP): $(COQLIGHT_DEP)

coqlight: coq-HoTT
	$(MKDIR_P) "$(BUILDCOQDIR)"
	$(MAKE) -f "$(SRCCOQDIR)/Makefile" --directory="$(BUILDCOQDIR)" coqlight

miniopt: coq-HoTT
	$(MKDIR_P) "$(BUILDCOQDIR)"
	$(MAKE) -f "$(SRCCOQDIR)/Makefile" --directory="$(BUILDCOQDIR)" miniopt

install-coqlight: coqlight
	$(MAKE) -f "$(SRCCOQDIR)/Makefile" --directory="$(BUILDCOQDIR)" install-coqlight

if make_ssreflect
clean-local: $(SSRMAKEFILE)
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(MAKE_COQBIN)/" clean
	rm -f "$(SSRMAKEFILE)"
endif

# The standard library files must be compiled in a special way
stdlib: $(STDVOFILES)

$(STDVOFILES) : %.vo : %.v $(LOCAL_COQTOP)
	$(TIMER) $(LOCAL_COQTOP) -indices-matter -boot -nois -coqlib $(SRCCOQLIB) -R $(SRCCOQLIB)/theories Coq -compile $(basename $<)


# The HoTT library as a single target
hottlib: $(VOFILES)

# A rule for compiling the HoTT libary files
if make_ssreflect
$(VOFILES) : %.vo : %.v $(STDVOFILES) $(SSRVOFILES) $(LOCAL_COQC)
	$(TIMER) $(HOQC) $<
else
$(VOFILES) : %.vo : %.v $(STDVOFILES) $(LOCAL_COQC)
	$(TIMER) $(HOQC) $<
endif

if make_ssreflect
# Compilation of ssreflect is a bit more roundabout because ssreflect relies on coq_makefile,
# which we do not. Perhaps we should. Anyhow, we circumvent the "standard" ssreflect procedure
# to keep track of dependencies and what should be installed where. This will break if ssreflect
# changes its compilation procedure drastically.
ssrplugin: stdlib $(SSRVOFILES)

$(SSRMAKEFILE): $(ssrdir)/Make $(LOCAL_COQMAKEFILE)
	$(LOCAL_COQMAKEFILE) COQC = "$(TIMER) $(HOQC)" -f "$(ssrdir)/Make" > "$(SSRMAKEFILE)"

$(SSRVOFILES): $(SRRMAKEFILE) $(SSRCMXSFILES) $(SSRCMAFILES)

$(SSRVOFILES) : %.vo : %.v
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(MAKE_COQBIN)/" $@

$(SSRCMXSFILES): $(SSRMAKEFILE)

$(SSRCMAFILES): $(SSRMAKEFILE)

$(SSRCMXSFILES): %.cmxs : %.mllib
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(MAKE_COQBIN)/" $@

$(SSRCMAFILES): %.cma : %.mllib
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(MAKE_COQBIN)/" $@
endif

# The HTML files
html: $(GLOBFILES) $(VFILES) $(STDGLOBFILES) $(STDVFILES) $(LOCAL_COQDOC)
	- $(mkdir_p) html
	$(LOCAL_COQDOC) -toc -interpolate -utf8 -html --coqlib_path $(SRCCOQLIB) --no-externals -R $(srcdir)/theories HoTT -R $(SRCCOQLIB)/theories Coq -d html $(VFILES) $(STDVFILES)

# The TAGS file
TAGS_FILES = $(STDVFILES) $(VFILES)
TAGS : $(TAGS_FILES)
	$(ETAGS) --language=none \
	-r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Proposition\)[[:space:]]+\([[:alnum:]_'\'']+\)/\2/' \
	-r '/^[[:space:]]*\([[:alnum:]_'\'']+\)[[:space:]]*:/\1/' \
	$^

# Dependency files
$(DEPFILES) $(STDDEPFILES) : %.d : %.v $(LOCAL_COQDEP)
	$(LOCAL_COQDEP) -nois -coqlib $(SRCCOQLIB) -R $(srcdir)/theories HoTT -R $(SRCCOQLIB)/theories Coq $< >$@

# install: install-coqlight

clean:
	rm -f $(CLEANFILES)
	find $(SRCCOQLIB)/theories $(srcdir)/theories -name \*.vo -o -name \*.glob | xargs rm -f

-include $(DEPFILES) $(STDDEPFILES)
