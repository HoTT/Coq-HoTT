# KNOWNTARGETS will not be passed along to Makefile.coq
KNOWNTARGETS := Makefile.coq
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

Makefile.coq: Makefile _CoqProject
# Generate _CoqProject file
	bash etc/generate_coqproject.sh
# Generate Makefile
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq

# We replace the html target with real-html, because we want to make
# the timestamp file.  We use patsubst rather than subst to do this so
# that we only replace entire words.
invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(patsubst html,real-html,$(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS)))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
