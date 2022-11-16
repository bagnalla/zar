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

* [zarpy](https://pypi.org/project/zarpy/) pip package (see [python/zar/test/test.py](python/zar/test/test.py) for an example
of using it after installation):
```
opam install pythonlib ppx_import ppx_deriving
cd python/zar/ocaml
dune build zar.so
cd ..
make install
```

* Extracted sampler analysis scripts (e.g., [analyze.py](extract/geometric/analyze.py)):
```
pip install numpy matplotlib scipy
```

## Foundational

* Axioms: [axioms.v](axioms.v)
* Extended reals: [eR.v](eR.v)
* Tactics: [tactics.v](tactics.v)

## cpGCL and cwp

* cpGCL syntax: [cpGCL.v](cpGCL.v)
* cwp semantics: [cwp.v](cwp.v)

## CF Trees

* CF trees: [tree.v](tree.v), [tcwp.v](tcwp.v), [tcwp_facts.v](tcwp_facts.v)
* Compiler from cpGCL to CF trees: [compile.v](compile.v), [cwp_tcwp.v](cwp_tcwp.v)
* De-biasing: [uniform.v](uniform.v), [debias.v](debias.v)

## Generating Interaction Trees

* Generating itrees: [itree.v](itree.v)

## Order/Domain Theory and Algebraic Coinduction

* Basic order theory: [order.v](order.v)
* CPOs: [cpo.v](cpo.v)
* Algebraic CPOs and comorphisms: [aCPO.v](aCPO.v)
* Cotrees: [cotree.v](cotree.v), [cocwp.v](cocwp.v), [cocwp_facts.v](cocwp_facts.v)

## Sampling Equidistribution Theorems

* Equidistribution theorems for itrees, cotrees, CF trees, and cpGCL: [equidistribution.v](equidistribution.v)

## Empirical Validation

[extract/](extract/) contains driver code and scripts for evaluating extracted samplers (e.g., [dueling coins](dueling_coins.v), [n-sided die](./die.v), [geometric distribution](geometric.v), [discrete gaussian](gaussian.v), [hare and tortoise](hare.v)).

[fast-loaded-dice-roller/](fast-loaded-dice-roller/) contains a clone of `https://github.com/probcomp/fast-loaded-dice-roller` modified to track entropy usage.

[optimal-approximate-sampling/](optimal-approximate-sampling/) contains a clone of `https://github.com/probcomp/optimal-approximate-sampling` modified to track entropy usage.

[python/zar/](python/zar/) contains the `zar` pip package source.

[python/tf/](python/tf/) contains the TensorFlow 2 project, with [batch_gen.py](python/tf/batch_gen.py) implementing a sampling-without-replacement generator on top of the `zar` sampler package.
