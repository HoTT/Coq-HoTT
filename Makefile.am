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
CAMERA := python proviola/camera/camera.py

# The list of files that comprise the HoTT library
VFILES=$(shell find "$(srcdir)/theories" -name "*.v")
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
DEPFILES:=$(VFILES:.v=.d)
HTMLUTF8FILES:=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html-utf8/HoTT.%,$(subst /,.,$(VFILES:.v=.html)))
HTMLFILES:=$(patsubst $(subst /,.,$(srcdir)).theories.%,$(srcdir)/html/HoTT.%,$(subst /,.,$(VFILES:.v=.html)))
XMLFILES:=$(patsubst $(srcdir)/html/%,$(srcdir)/proviola-xml/%,$(HTMLFILES:.html=.xml))
PROVIOLA_HTMLFILES:=$(patsubst $(srcdir)/proviola-xml/%,$(srcdir)/proviola-html/%,$(XMLFILES:.xml=.html))

# The list of files that comprise the alternative standard library
STDVFILES=$(shell find "$(SRCCOQLIB)/theories" -name "*.v")
STDVOFILES:=$(STDVFILES:.v=.vo)
STDGLOBFILES:=$(STDVFILES:.v=.glob)
STDDEPFILES:=$(STDVFILES:.v=.d)
STDHTMLUTF8FILES:=$(patsubst $(subst /,.,$(srcdir)).coq.theories.%,$(srcdir)/html-utf8/Coq.%,$(subst /,.,$(STDVFILES:.v=.html)))
STDHTMLFILES:=$(patsubst $(subst /,.,$(srcdir)).coq.theories.%,$(srcdir)/html/Coq.%,$(subst /,.,$(STDVFILES:.v=.html)))
STDXMLFILES:=$(patsubst $(srcdir)/html/%,$(srcdir)/proviola-xml/%,$(STDHTMLFILES:.html=.xml))
STDPROVIOLA_HTMLFILES:=$(patsubst $(srcdir)/proviola-xml/%,$(srcdir)/proviola-html/%,$(STDXMLFILES:.xml=.html))

if make_ssreflect
# The list of Coq files that comprise ssreflect
SSRMAKEFILE=$(srcdir)/Makefile_ssrplugin
ssrdir=$(srcdir)/ssrplugin
SSRVFILES=$(shell find "$(ssrdir)/theories" -name "*.v")
SSRVOFILES=$(SSRVFILES:.v=.vo)
SSRGLOBFILES=$(SSRVFILES:.v=.glob)
SSRHTMLFILES:=$(SSRVFILES:.v=.html)
SSRMLIFILES=$(shell find "$(ssrdir)/src" -name "*.mli")
SSRMLFILES=$(shell find "$(ssrdir)/src" -name "*.ml4" -o -name "*.ml")
SSRMLLIBFILES=$(shell find "$(ssrdir)/theories" -name "*.mllib")
SSRCMXSFILES=$(SSRMLLIBFILES:.mllib=.cmxs)
SSRCMAFILES=$(SSRMLLIBFILES:.mllib=.cma)
endif

# Definitions that let autoconf know how to install things.
nobase_hott_DATA = \
	$(VOFILES) \
	$(STDVOFILES) \
	$(shell find "$(SRCCOQLIB)/theories" -name "README.txt") \
	$(SSRVOFILES) \
	$(SSRCMXSFILES) \
	$(SSRCMAFILES)

# The Coq compiler, adapted to HoTT
HOQC=$(srcdir)/hoqc

# Which files should be cleaned
CLEANFILES = $(VOFILES) $(GLOBFILES) $(STDVOFILES) $(STDGLOBFILES) $(DEPFILES) $(STDDEPFILES) $(HTMLFILES) $(STDHTMLFILES) $(XMLFILES) $(STDXMLFILES) $(PROVIOLA_HTMLFILES) $(STDPROVIOLA_HTMLFILES) html-done.timestamp

if make_ssreflect
.PHONY: stdlib hottlib clean html proviola clean-local install-data-local proviola-all proviola-xml html-utf8 ssrplugin
else
.PHONY: stdlib hottlib clean html proviola clean-local install-data-local proviola-all proviola-xml html-utf8
endif

# TODO(JasonGross): Get this to work on Windows, where symlinks are unreliable
install-data-local:
	$(MKDIR_P) "$(hottdir)/coq"
	rm -f "$(hottdir)/coq/dev" "$(hottdir)/coq/plugins"
	$(LN_S) "$(COQLIB)/dev" "$(hottdir)/coq"
	$(LN_S) "$(COQLIB)/plugins" "$(hottdir)/coq"

if make_ssreflect
clean-local: $(SSRMAKEFILE)
	$(MAKE) -f "$(SSRMAKEFILE)" COQBIN="$(COQBIN)/" clean
	rm -f "$(SSRMAKEFILE)"
endif

# The standard library files must be compiled in a special way
stdlib: $(STDVOFILES)

$(STDVOFILES) : %.vo : %.v
	$(VECHO) COQTOP $(basename $<)
	$(Q) $(TIMER) "$(COQTOP)" -indices-matter -boot -nois -coqlib "$(SRCCOQLIB)" -R "$(SRCCOQLIB)/theories" Coq -compile "$(basename $<)"


# The HoTT library as a single target
hottlib: $(VOFILES)

# A rule for compiling the HoTT libary files
if make_ssreflect
$(VOFILES) : %.vo : %.v $(STDVOFILES) $(SSRVOFILES)
	$(VECHO) HOQC $<
	$(Q) $(TIMER) $(HOQC) $<
else
$(VOFILES) : %.vo : %.v $(STDVOFILES)
	$(VECHO) HOQC $<
	$(Q) $(TIMER) $(HOQC) $<
endif

if make_ssreflect
# Compilation of ssreflect is a bit more roundabout because ssreflect relies on coq_makefile,
# which we do not. Perhaps we should. Anyhow, we circumvent the "standard" ssreflect procedure
# to keep track of dependencies and what should be installed where. This will break if ssreflect
# changes its compilation procedure drastically.
ssrplugin: stdlib $(SSRVOFILES)

$(SSRMAKEFILE): $(ssrdir)/Make
	$(COQMAKEFILE) COQC = "$(SILENCE_HOQC)\$$(TIMER) \"$(HOQC)\"" COQDEP = "$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f "$(ssrdir)/Make" > "$(SSRMAKEFILE)"

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

# The HTML files
# We have a dummy file, to allow us to depend on the html files without
# remaking them every time, and to prevent make -j2 from running coqdoc
# twice.
html-done.timestamp: $(GLOBFILES) $(VFILES) $(STDGLOBFILES) $(STDVFILES)
	- $(mkdir_p) html
	touch html-done.timestamp
	"$(COQDOC)" -toc -interpolate -html --coqlib_path "$(SRCCOQLIB)" --no-externals -R "$(srcdir)/theories" HoTT -R "$(SRCCOQLIB)/theories" Coq -d html $(VFILES) $(STDVFILES)

html:
	rm -f html-done.timestamp
	$(MAKE) html-done.timestamp

html-utf8: $(GLOBFILES) $(VFILES) $(STDGLOBFILES) $(STDVFILES)
	- $(mkdir_p) html-utf8
	"$(COQDOC)" -toc -interpolate -utf8 -html --coqlib_path "$(SRCCOQLIB)" --no-externals -R "$(srcdir)/theories" HoTT -R "$(SRCCOQLIB)/theories" Coq -d html $(VFILES) $(STDVFILES)



$(HTMLFILES) $(STDHTMLFILES) html/index.html html/coqdoc.css : html-done.timestamp


# the proviola files
proviola-html/index.html proviola-html/toc.html proviola-html/coqdoc.css : proviola-html/% : html/%
	- $(mkdir_p) proviola-html
	cp -f $< $@

proviola-html/proviola.css : proviola-html/% : proviola/proviola/coq/%
	- $(mkdir_p) proviola-html
	cp -f $< $@

proviola-xml/proviola.css proviola-xml/proviola.xsl : proviola-xml/% : proviola/proviola/coq/%
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

proviola: $(PROVIOLA_HTMLFILES) $(STDPROVIOLA_HTMLFILES) proviola-html/proviola.css proviola-html/toc.html proviola-html/coqdoc.css proviola-html/index.html

proviola-xml: $(XMLFILES) $(STDXMLFILES)

proviola-all: proviola proviola-xml


# The TAGS file
TAGS_FILES = $(STDVFILES) $(VFILES)
TAGS : $(TAGS_FILES)
	$(ETAGS) --language=none \
	-r '/^[[:space:]]*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Let\|Inductive\|Coinductive\|Proposition\)[[:space:]]+\([[:alnum:]_'\'']+\)/\2/' \
	-r '/^[[:space:]]*\([[:alnum:]_'\'']+\)[[:space:]]*:/\1/' \
	$^

# Dependency files
$(DEPFILES) $(STDDEPFILES) : %.d : %.v
	$(VECHO) COQDEP $<
	$(Q) "$(COQDEP)" -nois -coqlib "$(SRCCOQLIB)" -R "$(srcdir)/theories" HoTT -R "$(SRCCOQLIB)/theories" Coq $< | sed s'#\\#/#g' >$@

clean:
	rm -f $(CLEANFILES)
	find "$(SRCCOQLIB)/theories" $(srcdir)/theories -name \*.vo -o -name \*.glob | xargs rm -f

-include $(DEPFILES) $(STDDEPFILES)
