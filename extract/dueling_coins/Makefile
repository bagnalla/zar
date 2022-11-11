default: init
	ocamlopt dueling_coins.cmx driver.ml
	./a.out

entropy: init
	ocamlopt dueling_coins.cmx entropy.ml
	./a.out

init:
	rm -f dueling_coins.mli
	ocamlopt dueling_coins.ml
