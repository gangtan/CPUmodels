# Note: you first need to install the flocq library under the flocq-2.1.0 directory;
# just go to that directory and follow the instructions in INSTALL

MODULES := Coqlib CommonTacs Maps Bits X86Syntax Monad Vector MSetsMore ParserArg Xform Regexp RESet GrammarType Grammar BiGrammar Parser Recognizer Decode Encode RTL FloatingAux X86Semantics SemTests DecodeBi_ins DecodeBi
# CheckDeterministic
VS 	:= $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%)
	coq_makefile -R . X86Model $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
