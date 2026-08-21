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
============

Dependencies
------------

* Rocq (>= 9.2)
* The Mathcomp library (>= 2.6.0)
* Mathcomp classical (>= 1.17.0)

Dependencies can be installed with OPAM (>= 2.0) by typing:

```
% opam repo add coq-released https://coq.inria.fr/opam/released
% opam install coq-core.9.0.1 rocq-mathcomp-algebra.2.6.0 rocq-mathcomp-classical
```

Compilation
-----------

Just type

```
% make
% make install
```
