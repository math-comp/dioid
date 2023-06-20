From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat bigop ssralg.

(******************************************************************************)
(* The algebraic structure of dioids, as described in:                        *)
(*   Michel Minoux, Michel Gondran.                                           *)
(*   'Graphs, Dioids and Semirings. New Models and Algorithms.'               *)
(*   Springer, 2008                                                           *)
(*                                                                            *)
(* This file defines for each structure its type, its builders                *)
(* and its canonical properties:                                              *)
(*                                                                            *)
(*   * Dioid (idempotent semi-rings):                                         *)
(*            Dioid.type == interface type for dioid structure.               *)
(* SemiRing_POrder_isDioid.Build D addxx le_def                               *)
(*                       == packs addxx into a Dioid; the carrier type R must *)
(*                          have both a GRIng.SemiRing and a POrder canonical *)
(*                          structure.                                        *)
(* POrder_isDioid.Build D addA addC add0l addxx mulA mul1l mul1r mulDl mulDr  *)
(*   mul0l mul0r addxx le_def                                                 *)
(*                       == build a Dioid structure from the algebraic        *)
(*                          properties of its operations.                     *)
(*                          The carrier type T must have a POrder canonical   *)
(*                          structure.                                        *)
(* Choice_isDioid.Build D addA addC add0l addxx mulA mul1l mul1r mulDl mulDr  *)
(*   mul0l mul0r addxx == build a Dioid structure from the algebraic          *)
(*                          properties of its operations.                     *)
(*                          The carrier type T must have a Choice canonical   *)
(*                          structure.                                        *)
(* [SubChoice_isSubDioid of R by <:] == idempotent mixin axiom for R when it  *)
(*                          is a subType of a dioid.                          *)
(*                                                                            *)
(*   * ComDioid:                                                              *)
(*         ComDioid.type == interface type for commutative dioid structure    *)
(* GRing.SemiRing_hasCommutativeMul.Build D mulC == packs mulC into a         *)
(*                          comDioidType; the carrier type D must have a      *)
(*                          Dioid canonical structure.                        *)
(* ComSemiRIng_POrder_isComDioid.Build D addxx le_def                         *)
(*                       == packs addxx into a ComDioid; the carrier type D   *)
(*                          must have both a Dioid and a POrder canonical     *)
(*                          structure.                                        *)
(* POrder_isComDioid.Build D addA addC add0l addxx mulA mulC mul1l mulDl      *)
(*          mul0l le_def == builds a ComDioid structure using the             *)
(*                          commutativity to reduce the number of proof       *)
(*                          obligations.                                      *)
(*                          The carrier type T must have a POrder canonical   *)
(*                          structure.                                        *)
(* Choice_isComDioid.Build D addA addC add0l addxx mulA mulC mul1l mulDl      *)
(*                 mul0l == builds a ComDioid structure using the             *)
(*                          commutativity to reduce the number of proof       *)
(*                          obligations.                                      *)
(*                          The carrier type T must have a Choice canonical   *)
(*                          structure.                                        *)
(* [SubChoice_isSubComDioid of D by <:] == commutativity mixin axiom for S    *)
(*                          when it is a subType of a commutative dioid.      *)
(*                                                                            *)
(* --> Notations are defined in scope dioid_scope (delimiter %D).             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope order_scope.

Declare Scope dioid_scope.
Delimit Scope dioid_scope with D.
Local Open Scope dioid_scope.

Import Order.Theory GRing.Theory.

HB.mixin Record SemiRing_POrder_isDioid d D
    of GRing.SemiRing D & Order.POrder d D := {
  adddd : @idempotent D +%R;
  le_def : forall (a b : D), (a <= b) = (a + b == b);
}.

#[short(type="dioidType")]
HB.structure Definition Dioid d :=
  { D of SemiRing_POrder_isDioid d D & GRing.SemiRing D & Order.POrder d D }.

#[short(type="dioidLatticeType")]
HB.structure Definition DioidLattice d :=
  { D of Dioid d D & Order.Lattice d D }.

#[short(type="dioidBLatticeType")]
HB.structure Definition DioidBLattice d :=
  { D of Dioid d D & Order.BLattice d D }.

#[short(type="dioidTLatticeType")]
HB.structure Definition DioidTLattice d :=
  { D of Dioid d D & Order.TLattice d D }.

#[short(type="dioidTBLatticeType")]
HB.structure Definition DioidTBLattice d :=
  { D of Dioid d D & Order.TBLattice d D }.

HB.factory Record POrder_isDioid d D of Order.POrder d D := {
  zero : D;
  add : D -> D -> D;
  one : D;
  mul : D -> D -> D;
  addA : associative add;
  addC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  mulA : associative mul;
  mul1d : left_id one mul;
  muld1 : right_id one mul;
  mulDl : left_distributive mul add;
  mulDr : right_distributive mul add;
  mul0d : left_zero zero mul;
  muld0 : right_zero zero mul;
  oner_neq0 : one != zero;
  le_def : forall (a b : D), (a <= b) = (add a b == b);
}.

HB.builders Context d D of POrder_isDioid d D.
HB.instance Definition _ := GRing.isSemiRing.Build D addA addC add0d
  mulA mul1d muld1 mulDl mulDr mul0d muld0 oner_neq0.
HB.instance Definition _ := SemiRing_POrder_isDioid.Build d D adddd le_def.
HB.end.

HB.factory Record SemiRing_isDioid (d : unit) D of GRing.SemiRing D := {
  adddd : @idempotent D +%R;
}.

HB.builders Context d D of SemiRing_isDioid d D.

Definition le_dioid (a b : D) := a + b == b.

Definition lt_dioid a b := (b != a) && le_dioid a b.

Lemma lt_def_dioid a b : lt_dioid a b = (b != a) && le_dioid a b.
Proof. by []. Qed.

Lemma le_refl_dioid : reflexive le_dioid.
Proof. by move=> a; rewrite /le_dioid adddd. Qed.

Lemma le_anti_dioid : antisymmetric le_dioid.
Proof.
by move=> a b /andP[]; rewrite /le => /eqP ? /eqP; rewrite addrC => <-.
Qed.

Lemma le_trans_dioid : transitive le_dioid.
Proof.
move=> a b c; rewrite /le_dioid => /eqP baa /eqP <-.
by rewrite -[in X in _ == X]baa addrA.
Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build d D
  le_refl_dioid le_anti_dioid le_trans_dioid.

Lemma le_def (a b : D) : (a <= b) = (a + b == b).
Proof. by []. Qed.

HB.instance Definition _ := SemiRing_POrder_isDioid.Build d D adddd le_def.

HB.end.

HB.factory Record Choice_isDioid (d : unit) D of Choice D := {
  zero : D;
  add : D -> D -> D;
  one : D;
  mul : D -> D -> D;
  addA : associative add;
  addC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  mulA : associative mul;
  mul1d : left_id one mul;
  muld1 : right_id one mul;
  mulDl : left_distributive mul add;
  mulDr : right_distributive mul add;
  mul0d : left_zero zero mul;
  muld0 : right_zero zero mul;
  oner_neq0 : one != zero;
}.

HB.builders Context d D of Choice_isDioid d D.
HB.instance Definition _ := GRing.isSemiRing.Build D addA addC add0d
  mulA mul1d muld1 mulDl mulDr mul0d muld0 oner_neq0.
HB.instance Definition _ := SemiRing_isDioid.Build d D adddd.
HB.end.

Section DioidTheory.

Variables (disp : unit) (D : dioidType disp).

Implicit Type a b c : D.

Lemma le0d a : (0%R <= a).
Proof. by rewrite le_def add0r. Qed.

Lemma led_add2r c : {homo +%R^~ c : a b / a <= b }.
Proof.
move => a b; rewrite !le_def => /eqP abb.
by rewrite addrCA -addrA adddd addrA [b + a]addrC abb.
Qed.

Lemma led_add2l c : {homo +%R c : a b / a <= b }.
Proof. move=> a b; rewrite !(addrC c); exact: led_add2r. Qed.

Lemma led_add a b c d : a <= c -> b <= d -> a + b <= c + d.
Proof. move=> Hac Hbd; exact/(le_trans (led_add2r _ Hac)) /led_add2l. Qed.

Lemma led_addl a b : a <= b + a.
Proof. by rewrite le_def addrCA adddd. Qed.

Lemma led_addr a b : a <= a + b.
Proof. by rewrite le_def addrA adddd. Qed.

Lemma led_addE a b c : (a + b <= c) = ((a <= c) && (b <= c)).
Proof.
apply/idP/idP => [ablec | /andP[]].
- by rewrite (le_trans (led_addr _ _) ablec) (le_trans (led_addl _ _) ablec).
- by rewrite 2!le_def => /eqP <- /eqP <-; rewrite addrCA addrA led_addr.
Qed.

Lemma led_mul2l c : {homo *%R c : a b / a <= b }.
Proof. by move=> a b; rewrite le_def => /eqP <-; rewrite mulrDr led_addr. Qed.

Lemma led_mul2r c : {homo *%R^~ c : a b / a <= b }.
Proof. by move=> a b; rewrite le_def => /eqP <-; rewrite mulrDl led_addr. Qed.

Lemma led_mul a b c d : a <= c -> b <= d -> a * b <= c * d.
Proof. move=> ac bd; exact/(le_trans (led_mul2r _ ac))/led_mul2l. Qed.

End DioidTheory.

#[short(type="comDioidType")]
HB.structure Definition ComDioid d := { D of GRing.ComSemiRing D & Dioid d D }.

HB.factory Record POrder_isComDioid d D of Order.POrder d D := {
  zero : D;
  add : D -> D -> D;
  one : D;
  mul : D -> D -> D;
  addA : associative add;
  addC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  mulA : associative mul;
  mulC : commutative mul;
  mul1d : left_id one mul;
  mulDl : left_distributive mul add;
  mul0d : left_zero zero mul;
  oner_neq0 : one != zero;
  le_def : forall (a b : D), (a <= b) = (add a b == b);
}.

HB.builders Context d D of POrder_isComDioid d D.

Lemma muld1 : right_id one mul.
Proof. by move=> x; rewrite mulC mul1d. Qed.

Lemma mulDr : right_distributive mul add.
Proof. by move=> x y z; rewrite mulC mulDl !(mulC x). Qed.

Lemma muld0 : right_zero zero mul.
Proof. by move=> x; rewrite mulC mul0d. Qed.

HB.instance Definition _ := POrder_isDioid.Build d D
  addA addC add0d adddd mulA mul1d muld1 mulDl mulDr mul0d muld0 oner_neq0 le_def.

HB.instance Definition _ := GRing.SemiRing_hasCommutativeMul.Build D mulC.

HB.end.

HB.factory Record Choice_isComDioid (d : unit) D of Choice D := {
  zero : D;
  add : D -> D -> D;
  one : D;
  mul : D -> D -> D;
  addA : associative add;
  addC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  mulA : associative mul;
  mulC : commutative mul;
  mul1d : left_id one mul;
  mulDl : left_distributive mul add;
  mul0d : left_zero zero mul;
  oner_neq0 : one != zero;
}.

HB.builders Context d D of Choice_isComDioid d D.

Lemma muld1 : right_id one mul.
Proof. by move=> x; rewrite mulC mul1d. Qed.

Lemma mulDr : right_distributive mul add.
Proof. by move=> x y z; rewrite mulC mulDl !(mulC x). Qed.

Lemma muld0 : right_zero zero mul.
Proof. by move=> x; rewrite mulC mul0d. Qed.

HB.instance Definition _ := Choice_isDioid.Build d D
  addA addC add0d adddd mulA mul1d muld1 mulDl mulDr mul0d muld0 oner_neq0.

HB.instance Definition _ := GRing.SemiRing_hasCommutativeMul.Build D mulC.

HB.end.

#[short(type="subDioidType")]
HB.structure Definition SubDioid d (D : dioidType d) (S : pred D) (d' : unit) :=
  { U of GRing.SubSemiRing D S U & @Order.SubPOrder d D S d' U & Dioid d' U }.

#[short(type="subDioidLatticeType")]
HB.structure Definition SubDioidLattice d (D : dioidLatticeType d) S d' :=
  { U of @SubDioid d D S d' U & @Order.Lattice d' U }.

#[short(type="subDioidBLatticeType")]
HB.structure Definition SubDioidBLattice d (D : dioidLatticeType d) S d' :=
  { U of @SubDioid d D S d' U & @Order.BLattice d' U }.

#[short(type="subDioidTLatticeType")]
HB.structure Definition SubDioidTLattice d (D : dioidLatticeType d) S d' :=
  { U of @SubDioid d D S d' U & @Order.TLattice d' U }.

#[short(type="subDioidTBLatticeType")]
HB.structure Definition SubDioidTBLattice d (D : dioidLatticeType d) S d' :=
  { U of @SubDioid d D S d' U & @Order.TBLattice d' U }.

HB.factory Record SubSemiRing_SubPOrder_isSubDioid d (D : dioidType d) S d' U
    of GRing.SubSemiRing D S U & @Order.SubPOrder d D S d' U := {}.

HB.builders Context d D S d' U of SubSemiRing_SubPOrder_isSubDioid d D S d' U.
Lemma adddd : @idempotent U +%R.
Proof. by move=> x; apply: val_inj; rewrite raddfD adddd. Qed.
Lemma le_def (a b : U) : (a <= b) = (a + b == b).
Proof. by rewrite leEsub le_def -rmorphD /= (inj_eq val_inj). Qed.
HB.instance Definition _ := SemiRing_POrder_isDioid.Build d' U adddd le_def.
HB.end.

HB.factory Record SubChoice_isSubDioid d (D : dioidType d) S (d' : unit) U
    of SubChoice D S U := {
  semiring_closed_subproof : semiring_closed S;
}.

HB.builders Context d (D : dioidType d) S d' U
  of SubChoice_isSubDioid d D S d' U.
HB.instance Definition _ := GRing.SubChoice_isSubSemiRing.Build D S U
  semiring_closed_subproof.
HB.instance Definition _ := Order.SubChoice_isSubPOrder.Build d D S d' U.
HB.instance Definition _ := SubSemiRing_SubPOrder_isSubDioid.Build d D S d' U.
HB.end.

#[short(type="subComDioidType")]
HB.structure Definition SubComDioid d (D : comDioidType d) (S : pred D) d' :=
  {U of @SubDioid d D S d' U & ComDioid d' U}.

HB.factory Record SubComSemiRing_SubPOrder_isSubComDioid d (D : comDioidType d)
  S (d' : unit) U of GRing.SubComSemiRing D S U & @Order.SubPOrder d D S d' U :=
  {}.

HB.builders Context d D S d' U
  of SubComSemiRing_SubPOrder_isSubComDioid d D S d' U.
HB.instance Definition _ := SubSemiRing_SubPOrder_isSubDioid.Build d D S d' U.
HB.end.

HB.factory Record SubChoice_isSubComDioid d (D : comDioidType d) S (d' : unit) U
    of SubChoice D S U := {
  semiring_closed_subproof : semiring_closed S
}.

HB.builders Context d (D : comDioidType d) S d' U
  of SubChoice_isSubComDioid d D S d' U.
HB.instance Definition _ := GRing.SubChoice_isSubComSemiRing.Build D S U
  semiring_closed_subproof.
HB.instance Definition _ := Order.SubChoice_isSubPOrder.Build d D S d' U.
HB.instance Definition _ := SubSemiRing_SubPOrder_isSubDioid.Build d D S d' U.
HB.end.

Notation "[ 'SubSemiRing_SubPOrder_isSubDioid' 'of' U 'by' <: ]" :=
  (SubSemiRing_SubPOrder_isSubDioid.Build _ _ _ _ U)
  (at level 0, format "[ 'SubSemiRing_SubPOrder_isSubDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubSemiRing_SubPOrder_isSubDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubSemiRing_SubPOrder_isSubDioid.Build _ _ _ disp U)
  (at level 0, format "[ 'SubSemiRing_SubPOrder_isSubDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubDioid' 'of' U 'by' <: ]" :=
  (SubChoice_isSubDioid.Build _ _ _ _ U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubDioid.Build _ _ _ disp U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubComSemiRing_SubPOrder_isSubComDioid' 'of' U 'by' <: ]" :=
  (SubComSemiRing_SubPOrder_isSubComDioid.Build _ _ _ _ U)
  (at level 0, format "[ 'SubComSemiRing_SubPOrder_isSubComDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubComSemiRing_SubPOrder_isSubComDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubComSemiRing_SubPOrder_isSubComDioid.Build _ _ _ disp U)
  (at level 0, format "[ 'SubComSemiRing_SubPOrder_isSubComDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComDioid' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComDioid.Build _ _ _ _ U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubComDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubComDioid.Build _ _ _ disp U (semiringClosedP _))
  (at level 0, format "[ 'SubChoice_isSubComDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.

(* begin hide *)

(* Testing subtype hierarchy
Section Test0.

Variables (d : unit) (T : choiceType) (S : {pred T}).

Inductive B := mkB x & x \in S.
Definition vB u := let: mkB x _ := u in x.

HB.instance Definition _ := [isSub for vB].
HB.instance Definition _ := [Choice of B by <:].

End Test0.

Section Test1.

Variables (d : unit) (R : dioidType d) (S : semiringClosed R).

HB.instance Definition _ := [SubChoice_isSubDioid of B S by <: with tt].

End Test1.

Section Test2.

Variables (d : unit) (R : comDioidType d) (S : semiringClosed R).

HB.instance Definition _ := [SubChoice_isSubComDioid of B S by <: with tt].

End Test2.

*)

(* end hide *)
