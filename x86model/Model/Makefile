# Note: you first need to install the flocq library under the flocq-2.1.0 directory;
# just go to that directory and follow the instructions in INSTALL

MODULES := Coqlib Tacs Maps Bits X86Syntax Monad Parser Decode RTL FloatingAux X86Semantics 
# CheckDeterministic
# CheckDeterministic now fails after adding decoding for floating-point instructions; need to fix this
VS 	:= $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%)
	echo $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
