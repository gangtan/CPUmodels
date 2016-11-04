MODULES := MIPSSyntax ParserArg Xform Regexp RESet GrammarType Grammar BiGrammar Parser Decode MIPSSemantics
VS 	:= $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -C ../shared
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%)
	echo $(VS)
	coq_makefile -R . MIPSModel -R ../shared Shared $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
