From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat bigop.
Require Import mathcomp.analysis.classical_sets.
Require Import HB_wrappers.

(******************************************************************************)
(* The algebraic structures of complete lattices                              *)
(*                                                                            *)
(* This file defines for each structure its type, its packers and its         *)
(* canonical properties:                                                      *)
(*                                                                            *)
(*   * CompleteLattice:                                                       *)
(*  CompleteLattice.type == interface type for complete lattice structure     *)
(* CompleteLattice_of_WrapLattice.Build set_join_is_lub                       *)
(*                       == builds a CompleteLattice structure from the       *)
(*                          algebraic properties of its operation.            *)
(*                          The carrier type T must have a WrapLattice        *)
(*                          canonical structure (see HB_wrappers.v).          *)
(* CompleteLattice_of_WrapPOrder.Build set_join_is_lub                        *)
(*                       == builds a CompleteLattice structure from the       *)
(*                          algebraic properties of its operation.            *)
(*                          The carrier type T must have a WrapPOrder         *)
(*                          canonical structure (see HB_wrappers.v).          *)
(*                                                                            *)
(* --> After declaring an instance of CompleteLattice on T using              *)
(*     CompleteLattice_of_WrapPOrder.Build the new latticeType instance must  *)
(*     be made canonical by hand:                                             *)
(*     <<                                                                     *)
(*     Canonical T_latticeType := [latticeType of T for T_is_a_WrapLattice].  *)
(*     >>                                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Local Open Scope order_scope.

Definition set_f_is_lub T (eM : Equality.mixin_of T)
           (oM : Order.POrder.mixin_of eM) (set_f : set T -> T) :=
    (forall (S : set T) x, S x -> Order.POrder.le oM x (set_f S))
    /\ (forall (S : set T) y,
           (forall x, S x -> Order.POrder.le oM x y) ->
           Order.POrder.le oM (set_f S) y).

HB.mixin Record CompleteLattice_of_WrapLattice T of WrapLattice T := {
  set_join : set T -> T;
  set_join_is_lub : set_f_is_lub wrap_porderMixin set_join;
}.

HB.factory Record CompleteLattice_of_WrapPOrder T of WrapPOrder T := {
  set_join : set T -> T;
  set_join_is_lub : set_f_is_lub wrap_porderMixin set_join;
}.

HB.builders Context T (f : CompleteLattice_of_WrapPOrder T).

  Canonical T_is_a_eqType := [eqType of T for T_is_a_WrapChoice].
  Canonical T_is_a_choiceType := [choiceType of T for T_is_a_WrapChoice].
  Canonical T_is_a_porderType := [porderType of T for T_is_a_WrapPOrder].

  Lemma set_join_ub S : (ubound S) (set_join S).
  Proof. rewrite -ubP => y Hy; exact: (proj1 set_join_is_lub). Qed.

  Lemma set_join_le_ub S x : (ubound S) x -> set_join S <= x.
  Proof. rewrite -ubP => Hx; exact/(proj2 set_join_is_lub)/Hx. Qed.

  Lemma set_join_set1 x : set_join [set x] = x.
  Proof.
  apply/le_anti; rewrite set_join_ub // andbC /=.
  by apply: set_join_le_ub; rewrite ub_set1.
  Qed.

  Lemma set_joinUl S S' : (ubound S) (set_join (S `|` S')).
  Proof.
  rewrite -ubP => y Hy.
  have: (S `|` S') y by left.
  move: y {Hy}; rewrite ubP; exact: set_join_ub.
  Qed.

  Lemma set_joinUr S S' : (ubound S') (set_join (S `|` S')).
  Proof. rewrite setUC; exact: set_joinUl. Qed.

  Lemma set_joinU_ge_l S S' : set_join S <= set_join (S `|` S').
  Proof. exact/set_join_le_ub/set_joinUl. Qed.

  Lemma set_joinU_ge_r S S' : set_join S' <= set_join (S `|` S').
  Proof. exact/set_join_le_ub/set_joinUr. Qed.

  Lemma set_joinU_le S S' x :
    set_join S <= x -> set_join S' <= x -> set_join (S `|` S') <= x.
  Proof.
  move=> HS HS'.
  apply: set_join_le_ub; rewrite -ubP => y [] Hy.
  - move: HS; exact/le_trans/set_join_ub.
  - move: HS'; exact/le_trans/set_join_ub.
  Qed.

  Definition set_meet S := set_join (lbound S).

  Lemma set_meet_lb S : (lbound S) (set_meet S).
  Proof.
  rewrite -lbP => y Hy.
  apply: set_join_le_ub; rewrite -ubP => z Hz.
  by move: y Hy; rewrite lbP.
  Qed.

  Lemma set_meet_ge_lb S x : (lbound S) x -> x <= set_meet S.
  Proof. move: x; rewrite ubP; exact: set_join_ub. Qed.

  Lemma set_meet_set1 x : set_meet [set x] = x.
  Proof.
  apply/le_anti; rewrite set_meet_lb //=.
  by apply: set_meet_ge_lb; rewrite lb_set1.
  Qed.

  Lemma set_meetUl S S' : (lbound S) (set_meet (S `|` S')).
  Proof.
  rewrite -lbP => y Hy.
  have: (S `|` S') y by left.
  move: y {Hy}; rewrite lbP; exact: set_meet_lb.
  Qed.

  Lemma set_meetUr S S' : (lbound S') (set_meet (S `|` S')).
  Proof. rewrite setUC; exact: set_meetUl. Qed.

  Lemma set_meetU_le_l S S' : set_meet (S `|` S') <= set_meet S.
  Proof. exact/set_meet_ge_lb/set_meetUl. Qed.

  Lemma set_meetU_le_r S S' : set_meet (S `|` S') <= set_meet S'.
  Proof. exact/set_meet_ge_lb/set_meetUr. Qed.

  Lemma set_meetU_ge S S' x :
    x <= set_meet S -> x <= set_meet S' -> x <= set_meet (S `|` S').
  Proof.
  move=> HS HS'.
  apply: set_meet_ge_lb; rewrite -lbP => y [] Hy.
  - exact/(le_trans HS)/set_meet_lb.
  - exact/(le_trans HS')/set_meet_lb.
  Qed.

  Definition join x y := set_join [set x; y].

  Definition meet x y := set_meet [set x; y].

  Lemma join_ge_l x y : x <= join x y.
  Proof. move: (@set_joinUl (set1 x) (set1 y)); rewrite -ubP; exact. Qed.

  Lemma join_ge_r x y : y <= join x y.
  Proof. move: (@set_joinUr (set1 x) (set1 y)); rewrite -ubP; exact. Qed.

  Lemma join_le x y z : x <= z -> y <= z -> join x y <= z.
  Proof. by move=> Hx Hy; apply: set_joinU_le; rewrite set_join_set1. Qed.

  Lemma set_joinU S S' : set_join (setU S S') = join (set_join S) (set_join S').
  Proof.
  apply/le_anti/andP; split.
  - apply: set_joinU_le; [exact: join_ge_l|exact: join_ge_r].
  - apply: join_le; [exact: set_joinU_ge_l|exact: set_joinU_ge_r].
  Qed.

  Lemma meet_le_l x y : meet x y <= x.
  Proof. move: (@set_meetUl (set1 x) (set1 y)); rewrite -lbP; exact. Qed.

  Lemma meet_le_r x y : meet x y <= y.
  Proof. move: (@set_meetUr (set1 x) (set1 y)); rewrite -lbP; exact. Qed.

  Lemma meet_ge x y z : z <= x -> z <= y -> z <= meet x y.
  Proof. by move=> Hx Hy; apply: set_meetU_ge; rewrite set_meet_set1. Qed.

  Lemma set_meetU S S' : set_meet (setU S S') = meet (set_meet S) (set_meet S').
  Proof.
  apply/le_anti/andP; split.
  - apply: meet_ge; [exact: set_meetU_le_l|exact: set_meetU_le_r].
  - apply: set_meetU_ge; [exact: meet_le_l|exact: meet_le_r].
  Qed.

  Lemma joinC : commutative join.
  Proof. by move=> x y; rewrite /join setUC. Qed.

  Lemma meetC : commutative meet.
  Proof. by move=> x y; rewrite /meet setUC. Qed.

  Lemma joinA : associative join.
  Proof.
  move=> x y z.
  by rewrite -{1}[x]set_join_set1 -set_joinU setUA set_joinU set_join_set1.
  Qed.

  Lemma meetA : associative meet.
  Proof.
  move=> x y z.
  by rewrite -{1}[x]set_meet_set1 -set_meetU setUA set_meetU set_meet_set1.
  Qed.

  Lemma joinK y x : meet x (join x y) = x.
  Proof.
  apply/le_anti; rewrite meet_le_l /=.
  apply: meet_ge => //; exact: join_ge_l.
  Qed.

  Lemma meetK y x : join x (meet x y) = x.
  Proof.
  apply/le_anti; rewrite join_ge_l andbC /=.
  apply: join_le => //; exact: meet_le_l.
  Qed.

  Lemma meet_le x y : (x <= y) = (meet x y == x).
  Proof.
  apply/idP/idP => [Hxy|/eqP <-]; [|exact: meet_le_r].
  by apply/eqP/le_anti; rewrite meet_le_l /= meet_ge.
  Qed.

  Definition completeLattice_latticeMixin :=
    LatticeMixin meetC joinC meetA joinA joinK meetK meet_le.

  HB.instance Definition to_WrapLattice_of_WrapPOrder :=
    WrapLattice_of_WrapPOrder.Build T completeLattice_latticeMixin.

  HB.instance Definition to_CompleteLattice_of_WrapLattice :=
    CompleteLattice_of_WrapLattice.Build T set_join_is_lub.

HB.end.

HB.structure Definition CompleteLattice :=
  { T of WrapLattice T & CompleteLattice_of_WrapLattice T }.

Coercion CompleteLattice_to_Equality (T : CompleteLattice.type) :=
  Eval hnf in [eqType of T for T].
Canonical CompleteLattice_to_Equality.
Coercion CompleteLattice_to_Choice (T : CompleteLattice.type) :=
  Eval hnf in [choiceType of T for T].
Canonical CompleteLattice_to_Choice.
Coercion CompleteLattice_to_POrder (T : CompleteLattice.type) :=
  Eval hnf in [porderType of T for T].
Canonical CompleteLattice_to_POrder.
Coercion CompleteLattice_to_Lattice (T : CompleteLattice.type) :=
  Eval hnf in [latticeType of T for T].
Canonical CompleteLattice_to_Lattice.

Section CompleteLatticeTheory.

Variables T : CompleteLattice.type.

Implicit Types S : set T.
Implicit Types x : T.

Lemma set_join_ub S : (ubound S) (set_join S).
Proof. move=> y Hy; exact: (proj1 set_join_is_lub). Qed.

Lemma set_join_le_ub S x : (ubound S) x -> set_join S <= x.
Proof. move=> Hx; exact/(proj2 set_join_is_lub)/Hx. Qed.

Lemma set_join_le_incl S S' : (S `<=` S')%classic -> set_join S <= set_join S'.
Proof. move=> H; apply: set_join_le_ub => x Hx; exact/set_join_ub/H. Qed.

Lemma set_join_unique S x :
  (ubound S) x -> (forall y, (ubound S) y -> x <= y) -> x = set_join S.
Proof.
move=> Hub Hlub; apply/le_anti; rewrite set_join_le_ub // andbC /=.
exact/Hlub/set_join_ub.
Qed.

Lemma set_join_set1 x : set_join [set x] = x.
Proof.
apply/le_anti; rewrite set_join_ub // andbC /=.
by apply: set_join_le_ub; rewrite ub_set1.
Qed.

Lemma set_joinUl S S' : (ubound S) (set_join (S `|` S')).
Proof.
move=> y Hy.
have: (S `|` S') y by left.
move: y {Hy}; rewrite ubP; exact: set_join_ub.
Qed.

Lemma set_joinUr S S' : (ubound S') (set_join (S `|` S')).
Proof. rewrite setUC; exact: set_joinUl. Qed.

Lemma set_joinU_ge_l S S' : set_join S <= set_join (S `|` S').
Proof. exact/set_join_le_ub/set_joinUl. Qed.

Lemma set_joinU_ge_r S S' : set_join S' <= set_join (S `|` S').
Proof. exact/set_join_le_ub/set_joinUr. Qed.

Lemma set_joinU_le S S' x :
  set_join S <= x -> set_join S' <= x -> set_join (S `|` S') <= x.
Proof.
move=> HS HS'.
apply: set_join_le_ub => y [] Hy.
- move: HS; exact/le_trans/set_join_ub.
- move: HS'; exact/le_trans/set_join_ub.
Qed.

Definition bottom : T := set_join set0.

Definition top : T := set_join setT.

Lemma bottom_minimum x : bottom <= x.
Proof. exact: set_join_le_ub. Qed.

Lemma top_maximum x : x <= top.
Proof. exact: set_join_ub. Qed.

Definition set_meet S := set_join (lbound S).

Lemma set_meet_lb S : (lbound S) (set_meet S).
Proof.
move=> y Hy.
apply: set_join_le_ub => z Hz.
by move: y Hy; rewrite lbP.
Qed.

Lemma set_meet_ge_lb S x : (lbound S) x -> x <= set_meet S.
Proof. move: x; rewrite ubP; exact: set_join_ub. Qed.

Lemma set_meet_le_incl S S' : (S `<=` S')%classic -> set_meet S' <= set_meet S.
Proof. move=> H; apply: set_meet_ge_lb => x Hx; exact/set_meet_lb/H. Qed.

Lemma set_meet_unique S x :
  (lbound S) x -> (forall y, (lbound S) y -> y <= x) -> x = set_meet S.
Proof.
move=> Hlb Hglb; apply/le_anti; rewrite set_meet_ge_lb //=.
exact/Hglb/set_meet_lb.
Qed.

Lemma set_meet_set1 x : set_meet [set x] = x.
Proof.
apply/le_anti; rewrite set_meet_lb //=.
by apply: set_meet_ge_lb; rewrite lb_set1.
Qed.

Lemma set_meetUl S S' : (lbound S) (set_meet (S `|` S')).
Proof.
rewrite -lbP => y Hy.
have: (S `|` S') y by left.
move: y {Hy}; rewrite lbP; exact: set_meet_lb.
Qed.

Lemma set_meetUr S S' : (lbound S') (set_meet (S `|` S')).
Proof. rewrite setUC; exact: set_meetUl. Qed.

Lemma set_meetU_le_l S S' : set_meet (S `|` S') <= set_meet S.
Proof. exact/set_meet_ge_lb/set_meetUl. Qed.

Lemma set_meetU_le_r S S' : set_meet (S `|` S') <= set_meet S'.
Proof. exact/set_meet_ge_lb/set_meetUr. Qed.

Lemma set_meetU_ge S S' x :
  x <= set_meet S -> x <= set_meet S' -> x <= set_meet (S `|` S').
Proof.
move=> HS HS'.
apply: set_meet_ge_lb; rewrite -lbP => y [] Hy.
- exact/(le_trans HS)/set_meet_lb.
- exact/(le_trans HS')/set_meet_lb.
Qed.

Lemma bottom_set_meet : bottom = set_meet setT.
Proof.
apply/le_anti; rewrite bottom_minimum /=.
apply: set_join_le_ub => x; exact.
Qed.

Lemma top_set_meet : top = set_meet set0.
Proof. by apply/le_anti; rewrite set_meet_ge_lb //= top_maximum. Qed.

Lemma join_def x y : Order.join x y = set_join [set x; y].
Proof.
apply/le_anti/andP; split; last first.
  by apply: set_joinU_le; rewrite set_join_set1; [exact: leUl|exact: leUr].
rewrite leUx.
rewrite -[X in X <= _](set_join_set1 x) set_joinU_ge_l /=.
by rewrite -[X in X <= _](set_join_set1 y) set_joinU_ge_r.
Qed.

Lemma meet_def x y : Order.meet x y = set_meet [set x; y].
Proof.
apply/le_anti/andP; split.
  by apply: set_meetU_ge; rewrite set_meet_set1; [exact: leIl|exact: leIr].
rewrite lexI.
rewrite -[X in _ <= X](set_meet_set1 x) set_meetU_le_l /=.
by rewrite -[X in _ <= X](set_meet_set1 y) set_meetU_le_r.
Qed.

Lemma set_joinU S S' : set_join (setU S S') = Order.join (set_join S) (set_join S').
Proof.
apply/le_anti/andP; split.
- apply: set_joinU_le; [exact: leUl|exact: leUr].
- by rewrite leUx set_joinU_ge_l set_joinU_ge_r.
Qed.

Lemma set_meetU S S' : set_meet (setU S S') = Order.meet (set_meet S) (set_meet S').
Proof.
apply/le_anti/andP; split.
- by rewrite lexI set_meetU_le_l set_meetU_le_r.
- apply: set_meetU_ge; [exact: leIl|exact: leIr].
Qed.

End CompleteLatticeTheory.
