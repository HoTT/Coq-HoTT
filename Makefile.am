ACLOCAL_AMFLAGS = -I etc
bin_PROGRAMS =
hott_SOURCES =
hott_DATA =
EXTRA_DIST = bin coq theories etc LICENSE.txt CREDITS.txt INSTALL.txt README.markdown
hottdir=$(datarootdir)/hott

# How to compile
# Arguments that need to be passed to Coq to make it HoTT valid
COQARGS:=-noinit -coqlib $(COQLIB) -relevant-equality -warn-universe-inconsistency

# The list of files that comprise the library in the order in which
# they should appear in the generated documentation.

VFILES=$(shell find theories -name "*.v")
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)

.PHONY: all .depend html latex pdf doc

all: .depend $(VOFILES) # doc

clean:
	echo WOULD REMOVE /bin/rm -f doc/html/* doc/latex/* `find $(srcdir)/theories -name "*.{vo,glob}"`

doc: html pdf

html: $(GLOBFILES)
	/bin/mkdir -p doc/html
	$(COQDOC) --html --toc --utf8 --charset utf8 --interpolate -d doc/html $(VFILES)
	/bin/cp -f homotopy.css doc/html/coqdoc.css
	echo +++++;\
	echo +++++ HMTL documentation doc/html was generated successfully;\
	echo +++++

latex: $(GLOBFILES)
	/bin/mkdir -p doc/latex
	$(COQDOC) --latex --toc --utf8 --charset utf8 --interpolate -o doc/latex/UnivalentFoundations.tex $(VFILES)
	if [ ! -f doc/latex/coqdoc.sty ] ; then echo coqdoc.sty not found, using my own; cp coqdoc.sty doc/latex; fi

pdf: latex
	if [ -x "`which latexmk`" ]; \
	then \
		echo Good, you have latexmk; \
		cd doc/latex; \
		latexmk -pdf UnivalentFoundations.tex; \
	else \
		echo Using pdflatex to generated PDF; \
		cd doc/latex; \
		pdflatex UnivalentFoundations.tex; \
		pdflatex UnivalentFoundations.tex; \
	fi
	echo +++++;\
	echo +++++ PDF document doc/latex/UnivalentFoundations.pdf was generated successfully;\
	echo +++++

.depend:
	$(COQDEP) -I theories $(VFILES) > .depend

%.vo %.glob: %.v
	$(COQTOP) -noinit $(COQARGS) $<

include .depend
