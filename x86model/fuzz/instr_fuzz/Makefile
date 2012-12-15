syntaxfuzzer.native: syntaxfuzzer.ml PrettyPrinter.ml
	ocamlbuild -verbose 1 -cflag -g -lflag -g syntaxfuzzer.native -lib unix -lib nums

extraction:: 
	echo 'Require Import X8x6Syntax. Extraction Blacklist String List. Recursive Extraction Library X86Syntax.' > tmp1.v
	make -C "../Model/"
	coqc Fuzz.v -I "../Model/"
	coqc tmp1.v -I "../Model/"
	cp Parser.ml_fastarray Parser.ml
	rm Parser.mli
	rm *.mli
	cp cZeven.ml Zeven.ml

clean::
	rm -rf _build/
