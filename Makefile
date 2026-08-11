# Wrapper around coq_makefile. `make` builds everything listed in _CoqProject.

all: Makefile.coq
	+@$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+@$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# Forward .vo targets to Makefile.coq.
%.vo: Makefile.coq
	+@$(MAKE) -f Makefile.coq $@

.PHONY: all clean
