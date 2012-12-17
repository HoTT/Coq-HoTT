ACLOCAL_AMFLAGS = -I etc

bin_SCRIPTS = hoqtop hoqc
if make_hoqide
  bin_SCRIPTS += hoqide
endif

hottdir=$(datarootdir)/hott
EXTRA_DIST = coq theories etc LICENSE.txt CREDITS.txt INSTALL.txt README.markdown

# The list of files that comprise the library
VFILES=$(shell find $(srcdir)/theories -name "*.v")
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)

# The list of files that comprise the alternative standard library
STDVFILES=$(shell find $(srcdir)/coq -name "*.v")
STDVOFILES:=$(STDVFILES:.v=.vo)
STDGLOBFILES:=$(STDVFILES:.v=.glob)

nobase_hott_DATA = $(VOFILES) $(STDVOFILES) $(shell find $(srcdir)/coq/theories -name "README.txt")

# The Coq compiler, adapted to HoTT
HOQC=$(srcdir)/hoqc

# Which files should be cleaned
CLEANFILES = $(VOFILES) $(GLOBFILES) $(STDVOFILES) $(STDGLOBFILES)

install-data-local:
	$(mkdir_p) $(hottdir)/coq
	rm -f $(hottdir)/coq/dev $(hottdir)/coq/plugins
	ln -s $(COQLIB)/dev $(hottdir)/coq
	ln -s $(COQLIB)/plugins $(hottdir)/coq

# The standard library files must be compiled in a special way
$(STDVOFILES) : %.vo : %.v
	$(COQTOP) -boot -nois -coqlib $(srcdir)/coq -R $(srcdir)/coq/theories Coq -compile $(basename $<)

# The standard library files must be compiled in a special way
$(STDGLOBFILES) : %.glob : %.v
	$(COQTOP) -boot -nois -R $(srcdir)/coq/theories Coq -compile $(basename $<)

# The HoTT files depend on the new standard library, but coqdep will not figure that out.
$(VOFILES) : $(STDVOFILES)

# A rule for compiling the HoTT libary files
$(VOFILES) : %.vo : %.v
	$(HOQC) $<

# Dependency files
%.d: %.v; $(COQDEP) -nois -coqlib $(srcdir)/coq -I theories -R coq/theories Coq $< >$@
-include $(VFILES:.v=.d) $(STDVFILES:.v=.d)
