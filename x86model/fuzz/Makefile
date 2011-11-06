fuzzgen.native: Fuzz.vo fuzzgen.ml
	ocamlbuild -cflag -g -lflag -g fuzzgen.native -lib unix -lib nums

Fuzz.vo: Fuzz.v
	coqc Fuzz.v -I "../Model/"

extract-nob::
	echo 'Require Import Fuzz. Extraction Blacklist String List. Recursive Extraction Library Fuzz.' > tmp1.v
	coqc Fuzz.v -I "../Model/"
	coqc tmp1.v -I "../Model/" 
	cp Parser.ml_fastarray Parser.ml
	rm Parser.mli 
	rm *.mli
	cp cZeven.ml Zeven.ml

extraction:: 
	echo 'Require Import Fuzz. Extraction Blacklist String List. Recursive Extraction Library Fuzz.' > tmp1.v
	make -C "../Model/"
	coqc Fuzz.v -I "../Model/"
	coqc tmp1.v -I "../Model/"
	cp Parser.ml_fastarray Parser.ml
	rm Parser.mli
	rm *.mli
	cp cZeven.ml Zeven.ml

clean::
	rm -rf _build/
