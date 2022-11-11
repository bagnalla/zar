PKG_NAME=zarpy
DLL=zarpy.so

.PHONY: build install test clean

build:
	# do 'dune build zarpy.so' in ocaml directory first
	# dune build ocaml/$(DLL)
	cp ocaml/_build/default/$(DLL) $(PKG_NAME)
	chmod 0777 $(PKG_NAME)/$(DLL)

install: build
	python3 setup.py build
	pip3 install .

test:
	python3 test/test.py

clean:
	# dune clean
	rm -rf ocaml/_build
	rm -rf build
	rm -rf __pycache__
	rm -rf .pytest_cache
	rm -rf $(PKG_NAME)/__pycache__
	rm -f $(PKG_NAME)/$(DLL)
	rm -f ocaml/.merlin
	rm -rf *.egg-info
