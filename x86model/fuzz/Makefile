all: test_step 

test_step: ./Fuzz.vo
	ocamlbuild -cflag -g -lflag -g fuzzgen.native -lib unix -lib nums


./Fuzz.vo: ./Fuzz.v
	echo 'Require Import Fuzz. Extraction Blacklist String List. Extraction Library Fuzz.' > tmp1.v
	make -C "../"
	coqc tmp1.v -I "../Model/"

./Fuzz.v:

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
	make -C "../"
	coqc Fuzz.v -I "../Model/"
	coqc tmp1.v -I "../Model/"
	cp Parser.ml_fastarray Parser.ml
	rm Parser.mli
	rm *.mli
	cp cZeven.ml Zeven.ml

opt::
	ocamlbuild -cflag -g -lflag -g test.native -lib unix -lib nums
	

clean::
	rm -rf _build/
