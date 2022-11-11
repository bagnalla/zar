default: init
	ocamlopt unix.cmxa uniform.cmx driver.ml
	./a.out

entropy: init
	ocamlopt uniform.cmx entropy.ml
	./a.out

init:
	rm -f uniform.mli
	ocamlopt uniform.ml
