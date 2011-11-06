extract:
	coqc extractor.v -I "../"
compile:
	ocamlbuild tests/test.native -libs nums -I "libs"
run:
	./test.native < tests/test.txt
clean:
	rm *.ml *.mli
	rm *.vo *.glob
	ocamlbuild -clean
