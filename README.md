# Zar

Paper: https://arxiv.org/abs/2211.06747

## Setup

* Coq development:
```
opam pin add coq 8.16.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-itree
make -j4
```

* [Zarpy](https://pypi.org/project/zarpy/) Python3 package (see [python/zar/test/test.py](python/zar/test/test.py) for an example
of using it after installation):
```
opam install pythonlib ppx_import ppx_deriving
cd python/zar/ocaml
dune build zarpy.so
cd ..
make install
```

* Extracted sampler analysis scripts (e.g., [analyze.py](extract/geometric/analyze.py)):
```
pip install numpy==1.24.2 scipy==1.10.1 tensorflow==2.11.0 optas==1.0.3
```

## Foundational

* Axioms: [axioms.v](theories/axioms.v)
* Extended reals: [eR.v](theories/eR.v)
* Tactics: [tactics.v](theories/tactics.v)

## cpGCL and cwp

* cpGCL syntax: [cpGCL.v](theories/cpGCL.v)
* cwp semantics: [cwp.v](theories/cwp.v)

## CF Trees

* CF trees: [tree.v](theories/tree.v), [tcwp.v](theories/tcwp.v), [tcwp_facts.v](theories/tcwp_facts.v)
* Compiler from cpGCL to CF trees: [compile.v](theories/compile.v), [cwp_tcwp.v](theories/cwp_tcwp.v)
* De-biasing: [uniform.v](theories/uniform.v), [debias.v](theories/debias.v)

## Generating Interaction Trees

* Generating itrees: [itree.v](theories/itree.v)

## Order/Domain Theory and Algebraic Coinductives

* Basic order theory: [order.v](theories/order.v)
* CPOs: [cpo.v](theories/cpo.v)
* Algebraic CPOs and continuous extensions: [aCPO.v](theories/aCPO.v)
* Cotrees: [cotree.v](theories/cotree.v), [cocwp.v](theories/cocwp.v), [cocwp_facts.v](theories/cocwp_facts.v)

## Sampling Equidistribution Theorems

* Equidistribution theorems for itrees, cotrees, CF trees, and cpGCL: [equidistribution.v](theories/equidistribution.v)

## Empirical Validation

[extract/](extract/) contains driver code and scripts for evaluating extracted samplers (e.g., [dueling coins](examples/dueling_coins.v), [n-sided die](examples/die.v), [geometric distribution](examples/geometric.v), [discrete gaussian](theories/gaussian.v), [hare and tortoise](examples/hare.v)).

[fast-loaded-dice-roller/](fast-loaded-dice-roller/) contains a clone of [https://github.com/probcomp/fast-loaded-dice-roller](https://github.com/probcomp/fast-loaded-dice-roller) modified to track entropy usage.

[optimal-approximate-sampling/](optimal-approximate-sampling/) contains a clone of [https://github.com/probcomp/optimal-approximate-sampling](https://github.com/probcomp/optimal-approximate-sampling) modified to track entropy usage.

[python/zar/](python/zar/) contains the [Zarpy](https://pypi.org/project/zarpy/) Python3 package source.

[python/tf/](python/tf/) contains the TensorFlow 2 project, with [batch_gen.py](python/tf/batch_gen.py) implementing a sampling-without-replacement generator on top of the [Zarpy](https://pypi.org/project/zarpy/) sampler package.
