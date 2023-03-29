default: init
	ocamlopt prog.cmx driver.ml
	./a.out

init:
	rm -f prog.mli
	ocamlopt prog.ml

clean:
	rm -f *.cmi *.cmx *.o a.out *.dat
