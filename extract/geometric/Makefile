default: init
	ocamlopt geometric.cmx driver.ml
	./a.out

entropy: init
	ocamlopt geometric.cmx entropy.ml
	./a.out

init:
	rm -f geometric.mli
	ocamlopt geometric.ml
