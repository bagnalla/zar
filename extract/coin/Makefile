default: init
	ocamlopt coin.cmx driver.ml
	./a.out

entropy: init
	ocamlopt coin.cmx entropy.ml
	./a.out

init:
	rm -f coin.mli
	ocamlopt coin.ml
