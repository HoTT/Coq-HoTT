# Edit the following parameter(s) if "make" fails to find the executables

# The directory which contains the Coq executables (leave it empty if
# coqc is in the PATH), for example on my Mac I would set
# COQBIN=/Applications/CoqIdE_8.3.app/Contents/Resources/bin/
# (note the trailing slash).
COQBIN=

# Edit below at your own risk
COQC:=$(COQBIN)coqc
COQDEP:=$(COQBIN)coqdep
COQDOC:=$(COQBIN)coqdoc

# The list of files that comprise the library in the order in which
# they should appear in the generated documentation.

VFILES:= Functions.v \
	 Paths.v \
	 Fibrations.v \
	 Contractible.v \
	 Equivalences.v \
	 UsefulEquivalences.v \
	 FiberEquivalences.v \
	 FiberSequences.v \
	 Funext.v \
         Univalence.v \
         UnivalenceImpliesFunext.v \
	 UnivalenceAxiom.v \
	 FunextEquivalences.v \
	 HLevel.v \
         Homotopy.v

VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)

.PHONY: all .depend html latex pdf doc

all: .depend $(VOFILES) # doc

clean:
	/bin/rm -f *~ *.vo *.glob *.~ doc/html/* doc/latex/*

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
	$(COQDEP) -I . $(VFILES) > .depend

%.vo %.glob: %.v
	$(COQC) $<

include .depend
