ACLOCAL_AMFLAGS = -I etc

bin_SCRIPTS = hoqtop hoqc
if make_hoqide
  bin_SCRIPTS += hoqide
endif
if make_hoqtopbyte
  bin_SCRIPTS += hoqtop.byte
endif

hottdir=$(datarootdir)/hott
EXTRA_DIST = coq theories ssrplugin etc LICENSE.txt CREDITS.txt INSTALL.txt README.markdown

# The list of files that comprise the HoTT library
VFILES=$(shell find $(srcdir)/theories -name "*.v")
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
DEPFILES:=$(VFILES:.v=.d)
HOTTMAKEFILE=$(srcdir)/Makefile.coq

# The list of files that comprise the alternative standard library
STDVFILES=$(shell find $(srcdir)/coq -name "*.v")
STDVOFILES:=$(STDVFILES:.v=.vo)
STDGLOBFILES:=$(STDVFILES:.v=.glob)
STDDEPFILES:=$(STDVFILES:.v=.d)

if make_ssreflect
# The list of Coq files that comprise ssreflect
SSRMAKEFILE=$(srcdir)/Makefile_ssrplugin
ssrdir=$(srcdir)/ssrplugin
SSRVFILES=$(shell find $(ssrdir)/theories -name "*.v")
SSRVOFILES=$(SSRVFILES:.v=.vo)
SSRGLOBFILES=$(SSRVFILES:.v=.glob)
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
	$(shell find $(srcdir)/coq/theories -name "README.txt") \
	$(SSRVOFILES) \
	$(SSRCMXSFILES) \
	$(SSRCMAFILES)

# The Coq compiler, adapted to HoTT
HOQC=$(srcdir)/hoqc

# The path to the Coq library in $(srcdir)
SRCCOQLIB=$(srcdir)/coq

# Which files should be cleaned
CLEANFILES = $(STDVOFILES) $(STDGLOBFILES) $(STDDEPFILES) $(HOTTMAKEFILE)

if make_ssreflect
.PHONY: stdlib hottlib ssrplugin
else
.PHONY: stdlib hottlib
endif

install-data-local:
	$(mkdir_p) $(hottdir)/coq
	rm -f $(hottdir)/coq/dev $(hottdir)/coq/plugins
	ln -s $(COQLIB)/dev $(hottdir)/coq
	ln -s $(COQLIB)/plugins $(hottdir)/coq

if make_ssreflect
clean-local: $(SSRMAKEFILE)
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(COQBIN)/" clean
	rm -f "$(SSRMAKEFILE)"
endif

# The standard library files must be compiled in a special way
stdlib: $(STDVOFILES)

$(STDVOFILES) : %.vo : %.v
	$(COQTOP) -indices-matter -boot -nois -coqlib $(SRCCOQLIB) -R $(SRCCOQLIB)/theories Coq -compile $(basename $<)


# The HoTT library as a single target
hottlib: $(VOFILES) $(HOTTMAKEFILE)

# A rule for compiling the HoTT libary files
if make_ssreflect
HOTT_MAKEFILE_DEPS = $(STDVOFILES) $(SSRVOFILES)
else
HOTT_MAKEFILE_DEPS = $(STDVOFILES)
endif

$(HOTTMAKEFILE) : $(HOTT_MAKEFILE_DEPS)
	$(COQMAKEFILE) $(VFILES) -R "$(srcdir)/theories" HoTT COQC = "\$$(TIMER) \"$(HOQC)\"" COQDEP = "\"\$$(COQBIN)coqdep\" -nois -coqlib $(srcdir)/coq -R $(SRCCOQLIB)/theories Coq" > "$(HOTTMAKEFILE)"

if make_ssreflect
# Compilation of ssreflect is a bit more roundabout because ssreflect relies on coq_makefile,
# which we do not. Perhaps we should. Anyhow, we circumvent the "standard" ssreflect procedure
# to keep track of dependencies and what should be installed where. This will break if ssreflect
# changes its compilation procedure drastically.
ssrplugin: stdlib $(SSRVOFILES)

$(SSRMAKEFILE): $(ssrdir)/Make
	$(COQMAKEFILE) COQC = "$(HOQC)" -f "$(ssrdir)/Make" > "$(SSRMAKEFILE)"

$(SSRVOFILES): $(SRRMAKEFILE) $(SSRCMXSFILES) $(SSRCMAFILES)

$(SSRVOFILES) : %.vo : %.v
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(COQBIN)/" $@

$(SSRCMXSFILES): $(SSRMAKEFILE)

$(SSRCMAFILES): $(SSRMAKEFILE)

$(SSRCMXSFILES): %.cmxs : %.mllib
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(COQBIN)/" $@

$(SSRCMAFILES): %.cma : %.mllib
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(COQBIN)/" $@
endif

# The TAGS file
TAGS_FILES = $(STDVFILES) $(VFILES)
TAGS : $(TAGS_FILES)
	$(ETAGS) --language=none \
	-r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Proposition\)[[:space:]]+\([[:alnum:]_'\'']+\)/\2/' \
	-r '/^[[:space:]]*\([[:alnum:]_'\'']+\)[[:space:]]*:/\1/' \
	$^

# Dependency files
$(STDDEPFILES) : %.d : %.v
	$(COQDEP) -nois -coqlib $(SRCCOQLIB) -R $(srcdir)/theories HoTT -R $(SRCCOQLIB)/theories Coq $< >$@

-include $(STDDEPFILES) $(HOTTMAKEFILE)

clean: $(HOTTMAKEFILE)
	$(MAKE) -f $(HOTTMAKEFILE) clean
	rm -f $(CLEANFILES)
	find $(SRCCOQLIB) -name \*.vo -o -name \*.glob | xargs rm -f
