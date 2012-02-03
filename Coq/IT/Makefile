# Edit the following parameter(s) if "make" fails to find the executables

# The directory which contains the Coq executables (leave it empty if
# coqc is in the PATH), for example on my Mac I would set
# COQBIN=/Applications/CoqIdE_8.3.app/Contents/Resources/bin/
# (note the trailing slash).
#
# alternatively you can pass these as arguments on the command line, e.g.
# make COQBIN=~/w/htt/coq-8.3pl2-vv/bin/ COQC=coqc.opt
#
COQBIN=

# Edit below at your own risk

COQC:=coqc
COQDEP:=coqdep

# instead of Add LoadPath we pass them to coqc/coqide/coqtop
COQINCLUDES:=-R "univalent_foundations/Generalities" "Foundations" \
	-R "univalent_foundations/hlevel1" "Foundations" \
	-R "univalent_foundations/hlevel2" "Foundations" \
	-R "identity/" "IT" \
	-R "inductive_types/" "IT" \
	-R "nat_as_w_type/" "IT" \
	-R "two_is_hinitial/" "IT" \
	-R "w_is_hinitial/" "IT"

# recursively find all .v files and compile them
VFILES:=$(shell find . -name '*.v')
VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)

.PHONY: all .depend clean

all: .depend coqidescript .dirlocals $(VOFILES)

.depend:
	@$(COQBIN)$(COQDEP) $(COQINCLUDES) -I . $(VFILES) > .depend

%.vo %.glob: %.v
	@echo Compiling $<
	$(COQBIN)$(COQC) $(COQINCLUDES) $<

clean:
	@rm -f coqidescript
	@rm -f $(VOFILES)
	@rm -f $(GLOBFILES)

# script to start coq ide with proper arguments (-R ...)
coqidescript:
	@echo "#!/bin/sh" > $@
	@echo 'exec $(COQBIN)coqide $(COQINCLUDES) $$@' >> $@
	@chmod +x $@

# similar script, but for proof general
.dirlocals:
	@echo ';; local settings for proof general' > $@
	@echo '((coq-mode . (' >> $@
	@echo '  (coq-prog-args . ("-emacs-U" $(COQINCLUDES)))' >> $@
	@echo '  (coq-prog-name . "$(COQBIN)coqtop")' >> $@
	@echo ')))' >> $@
	@# we need to quote -R in elisp
	@sed -e 's/-R/"-R"/g' --in-place $@

-include .depend
