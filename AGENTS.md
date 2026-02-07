# Repository Guidelines

## Project Structure & Module Organization
This repository is centered on Coq proofs and verified samplers.
- Root `*.v` files: core formalization (`cpGCL.v`, `cwp.v`, `tree.v`, `uniform.v`, etc.).
- `examples/`: non-core Coq example programs and extraction-focused proofs (`examples/die.v`, `examples/tutorial.v`, etc.).
- `archive/`: historical/scratch Coq files kept for reference.
- `_CoqProject`, `Makefile`, `Makefile.conf`: Coq build configuration.
- `extract/`: extracted OCaml samplers, per-example `Makefile`s, and analysis scripts.
- `python/zar/`: Zarpy Python package wrapping extracted OCaml code.
- `fast-loaded-dice-roller/` and `optimal-approximate-sampling/`: vendored/modified comparison samplers with their own tests.

## Build, Test, and Development Commands
- `make -j4`: compile the main Coq development.
- `make clean` / `make cleanall`: remove build artifacts (standard / deep clean).
- `make validate`: run `coqchk` on built `.vo` files.
- `make quick` (alias for `make vio`): faster proof-checking during iteration.
- `cd python/zar && make install`: build and install the Zarpy package locally.
- `cd fast-loaded-dice-roller && ./check.sh`: build and run FLDR tests (`pytest` + `scipy`).
- `cd optimal-approximate-sampling && ./check.sh`: run OptAS Python tests and C crash test.

## Coding Style & Naming Conventions
- Coq: use 2-space indentation, keep lines readable, and follow existing notation/scoping patterns (`Local Open Scope ...`).
- Prefer descriptive theorem/definition names in `snake_case`; keep constructor/type names consistent with existing style (`CamelCase` where already used).
- Python: follow PEP 8 style and `snake_case`; tests follow `test_*.py`.
- No repository-wide formatter is configured; match surrounding file style exactly.

## Testing Guidelines
- Treat `make -j4` + `make validate` as the baseline for Coq changes.
- For sampler/runtime changes, run the relevant subproject checks (`./check.sh`).
- Stochastic tests use goodness-of-fit checks; occasional borderline failures can happen, so rerun before concluding regression.
