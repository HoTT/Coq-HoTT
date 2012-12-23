ACLOCAL_AMFLAGS = -I etc

bin_SCRIPTS = hoqtop hoqc
if make_hoqide
  bin_SCRIPTS += hoqide
endif

hottdir=$(datarootdir)/hott
EXTRA_DIST = coq theories etc LICENSE.txt CREDITS.txt INSTALL.txt README.markdown

# The list of files that comprise the HoTT library
VFILES=$(shell find $(srcdir)/theories -name "*.v")
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
DEPFILES:=$(VFILES:.v=.d)

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
CLEANFILES = $(VOFILES) $(GLOBFILES) $(STDVOFILES) $(STDGLOBFILES) $(DEPFILES) $(STDDEPFILES)

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


# The HoTT files depend on the new standard library and ssreflect, but coqdep will not figure that out.
hottlib: $(VOFILES)

# A rule for compiling the HoTT libary files
if make_ssreflect
$(VOFILES) : %.vo : %.v ssrplugin stdlib
	$(HOQC) $<
else
$(VOFILES) : %.vo : %.v stdlib
	$(HOQC) $<
endif


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

# Dependency files
$(DEPFILES) $(STDDEPFILES) : %.d : %.v
	$(COQDEP) -nois -coqlib $(srcdir)/coq -R theories HoTT -R coq/theories Coq $< >$@

-include $(DEPFILES) $(STDDEPFILES)
