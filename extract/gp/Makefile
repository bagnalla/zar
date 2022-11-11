default: init
	ocamlopt gp.cmx driver.ml
	./a.out

entropy: init
	ocamlopt gp.cmx entropy.ml
	./a.out

init:
	rm -f gp.mli
	ocamlopt gp.ml
