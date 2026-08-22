# Wrapper around coq_makefile. `make` builds everything listed in _CoqProject.

all: Makefile.coq
	+@$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+@$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# Forward .vo targets to Makefile.coq. FORCE makes the recursive make
# always run, so that Makefile.coq's own dependency tracking decides
# (a plain pattern rule would consider an existing .vo up to date).
%.vo: Makefile.coq FORCE
	+@$(MAKE) -f Makefile.coq $@

FORCE:

.PHONY: all clean FORCE
