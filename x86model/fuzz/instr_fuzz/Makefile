syntaxfuzzer.native: syntaxfuzzer.ml PrettyPrinter.ml enc_dec.ml
	ocamlbuild -verbose 1 -cflag -g -lflag -g syntaxfuzzer.native -lib unix -lib nums -Is extract

debugging: extraction
	ocamlbuild -use-ocamlfind -Is ocamlutil,extract -cflag -g -lflag -g main.native

profiling: extraction
	ocamlbuild -use-ocamlfind -Is ocamlutil,extract -cflag -g -lflag -g main.p.native

extraction::
	cd extract; make extraction; cd ..

clean::
	ocamlbuild -clean
	cd extract; make clean; cd ..
	rm -f *.glob *.vo 
