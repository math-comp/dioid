[![CI](https://github.com/math-comp/dioid/workflows/CI/badge.svg?branch=master)](https://github.com/math-comp/dioid/actions?query=workflow%3ACI)

Definitions of the algebraic structure of dioid following the style of
ssralg in the Mathcomp library.

The main algebraic structures defined are:
* dioids: idempotent semirings (i.e., forall x, x + x = x)
* complete dioids: dioids whose canonical order (x <= y wen x + y = y)
  yields a compelete lattice
* commutative variants (multiplicative law is commutative)

More details can be found in comments at the beginning of each .v file.

Installation
------------

This is currently not available as an OPAM (>= 2.0) package:

When MathComp Analysis for MathComp 2 will be released, this will be
installable by typing:

```
% opam repo add coq-released https://coq.inria.fr/opam/released
% opam install coq-mathcomp-dioid
```

Dependencies
------------

* Coq (>= 8.16)
* The Mathcomp library (>= 2.0.0)
* Hierarchy Builder (= 1.4.0)
* Mathcomp Analysis (hierarchy-builder branch)

Dependencies can be installed with OPAM (>= 2.0) by typing:

```
% opam repo add coq-released https://coq.inria.fr/opam/released
% opam install coq-mathcomp-algebra.2.0.0
```

Except MathComp Analysis (or only its mathcomp-classical package) that
must currently be installed from source:

```
% git clone https://github.com/math-comp/analysis
% git checkout hierarchy-builder
% make -j4 -C classical
% make -C classical install
```

Compilation
-----------

Just type

```
% make
```
