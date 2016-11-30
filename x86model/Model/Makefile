MODULES := X86Syntax ParserArg Xform Regexp RESet GrammarType Grammar BiGrammar Parser Recognizer X86BG_ins X86BG Encode X86Semantics SemTests Decode
# CheckDeterministic
VS 	:= $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -C ../../shared
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS:%=%)
	coq_makefile -R . X86Model -R ../../shared Shared $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
