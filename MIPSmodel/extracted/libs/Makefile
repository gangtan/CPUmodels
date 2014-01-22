all: test_step 

test_step: ../../Model/Parser.vo ../../Model/Decode.vo ../../Model/X86Semantics.vo 
	ocamlbuild -cflag -g -lflag -g test.native -lib unix -lib nums


../../Model/X86Semantics.vo: ../../Model/X86Semantics.v
	make -C "../../Model/"
	coqc extract.v -I "../../Model/"

../../Model/X86Semantics.v:

compile:
	ocamlbuild test.native -libs nums -I "libs"

extract-nob::
	coqc extract.v -I "../../Model/"
	#cp Parser.ml_fastarray Parser.ml
	#rm Parser.mli Decode.mli

extraction:: 
	coqc extract.v -I "../../Model/"

clean::
	rm -rf _build/
