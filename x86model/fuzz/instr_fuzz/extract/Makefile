all: test

test:
	ocamlbuild -cflag -g -lflag -g test.native -lib unix -lib nums

profiling::
	ocamlbuild -cflag -g -lflag -g test.p.native -lib unix -lib nums

extraction:: 
	coqc extract.v -I "../../../Model/"
	cp patch/*.ml .
	rm Parser.mli Decode.mli

clean::
	rm -f *.ml *.mli *.glob *.vo 
