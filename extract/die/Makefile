default: init
	ocamlopt die.cmx driver.ml
	./a.out

entropy: init
	ocamlopt die.cmx entropy.ml
	./a.out

init:
	rm -f die.mli
	ocamlopt die.ml
