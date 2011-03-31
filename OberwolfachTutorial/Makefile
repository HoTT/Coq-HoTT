# A simple Makefile which helps organize generation of documents and compilation
# of Coq files. This Makefile works only if each Coq file can be compiled independently
# of the others, i.e., we do not import and file from any other file. The coq_makefile
# and coqdep utilities can be used to generate more complex Makefiles.

# You may have to configure the following variables by providing the
# exact location of the executable, for example, something like
#
# COQC=/Applications/CoqIdE_8.3.app/Contents/Resources/bin/coqc

COQC=coqc
COQDOC=coqdoc
PDFLATEX=pdflatex

# The default target compiles the Coq files and generated the documentation.
default: *.vo doc

# A general rule explaining how to compile a .v file to .vo file.
%.vo: %.v
	$(COQC) $<

doc:
	$(PDFLATEX) cheatsheet.tex
	$(COQDOC) --latex --utf8 -s --body-only -o univalence_body.tex univalence.v
	$(PDFLATEX) univalence.tex
	$(PDFLATEX) univalence.tex

clean:
	/bin/rm -f *~ *.{aux,log,vo,glob,out} univalence_body.tex
