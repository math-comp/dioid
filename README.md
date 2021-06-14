[![CI](https://github.com/math-comp/dioid/workflows/CI/badge.svg?branch=master)](https://github.com/math-comp/dioid/actions?query=workflow%3ACI)

Definitions of the algebraic structure of dioid following the style of
ssralg in the Mathcomp library.

The main algebraic structures defined are:
* semirigns: rings without oppositve for the additive law
* dioids: idempotent semirings (i.e., forall x, x + x = x)
* complete dioids: dioids whose canonical order (x <= y wen x + y = y)
  yields a compelete lattice
* commutative variants (multiplicative law is commutative)

More details can be found in comments at the beginning of each file.

Installation
------------

This is available as an OPAM (>= 2.0) package:

```
% opam repo add coq-released https://coq.inria.fr/opam/released
% opam install coq-mathcomp-dioid
```

Dependencies
------------

* Coq (>= 8.13)
* The Mathcomp library (>= 1.12.0)
* Hierarchy Builder (= 1.0.0)
* Mathcomp Analysis (>= 0.3.9)

Dependencies can be installed with OPAM (>= 2.0) by typing:

```
% opam repo add coq-released https://coq.inria.fr/opam/released
% opam install coq-mathcomp-ssreflect.1.12.0 coq-hierarchy-builder.1.0.0 coq-mathcomp-analysis.0.3.5
```

Compilation
-----------

Just type

```
% make
```
