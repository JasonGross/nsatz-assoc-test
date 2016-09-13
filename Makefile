all: Makefile.coq

Makefile.coq: _CoqProject
	"$(COQBIN)coq_makefile" -f _CoqProject -o $@.bak && mv -f $@.bak $@

-include Makefile.coq
