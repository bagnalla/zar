default: init
	ocamlopt findist.cmx driver.ml
	./a.out

entropy: init
	ocamlopt findist.cmx entropy.ml
	./a.out

init:
	rm -f findist.mli
	ocamlopt findist.ml
