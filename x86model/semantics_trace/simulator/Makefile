all: test_step 

test_step: ../../Model/X86Semantics.vo 
	ocamlbuild -cflag -g -lflag -g test.native -lib unix -lib nums


../../Model/X86Semantics.vo: ../../Model/X86Semantics.v
	echo 'Require Import X86Semantics. Extraction Blacklist String List. Extraction Library X86Semantics.' > tmp1.v
	make -C "../../Model/"
	coqc tmp1.v -I "../../Model/"

../../Model/X86Semantics.v:

extract-nob::
	echo 'Require Import X86Semantics. Extraction Blacklist String List. Recursive Extraction Library X86Semantics.' > tmp1.v
	coqc tmp1.v -I "../../Model/"
	cp Parser.ml_fastarray Parser.ml
	rm Parser.mli Decode.mli
	cp cZeven.ml Zeven.ml

extraction:: 
	echo 'Require Import X86Semantics. Extraction Blacklist String List. Recursive Extraction Library X86Semantics.' > tmp1.v
	make -C "../../Model/"
	coqc tmp1.v -I "../../Model/"
	cp Parser.ml_fastarray Parser.ml
	rm Parser.mli Decode.mli
	cp cZeven.ml Zeven.ml

clean::
	rm -rf _build/
