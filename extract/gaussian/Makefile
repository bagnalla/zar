default: init
	ocamlopt sampler.cmx driver.ml
	./a.out

entropy: init
	ocamlopt sampler.cmx entropy.ml
	./a.out

init:
	rm -f sampler.mli
	ocamlopt sampler.ml
