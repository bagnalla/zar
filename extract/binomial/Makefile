default: init
	ocamlopt pascal.cmx driver.ml
	./a.out

entropy: init
	ocamlopt pascal.cmx entropy.ml
	./a.out

init:
	rm -f pascal.mli
	ocamlopt pascal.ml
