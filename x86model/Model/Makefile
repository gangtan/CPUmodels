MODULES := Coqlib Tacs Maps Bits X86SyntaxWithFloat Monad Parser DecodeWithFloat RTLWithFloat X86SemanticsWithFloat CheckDeterministic  
# DFACorrectness FastVerifier X86Lemmas VerifierCorrectness
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
