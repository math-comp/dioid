Definitions of the algebraic structure of dioid following the style of
ssralg in the Mathcomp library.

The main algebraic structures defined are:
* semirigns: rings without oppositve for the additive law
* dioids: idempotent semirings (i.e., forall x, x + x = x)
* complete dioids: dioids whose canonical order (x <= y wen x + y = y)
  yields a compelete lattice
* commutative variants (multiplicative law is commutative)

More details can be found in comments at the beginning of each file.

Dependencies
------------

* Coq (>= 8.10)
* The Mathcomp library (>= 1.9)

Dependencies can be installed with OPAM (>= 2.0) by typing:

```
% opam repo add coq-released https://coq.inria.fr/opam/released
% opam install coq-mathcomp-ssreflect
```

Compilation
-----------

Just type

```
% make
```
