From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat bigop.
Require Import HB_wrappers.

(******************************************************************************)
(* The algebraic structures of semi-rings and dioids, as described in:        *)
(*   Michel Minoux, Michel Gondran.                                           *)
(*   'Graphs, Dioids and Semirings. New Models and Algorithms.'               *)
(*   Springer, 2008                                                           *)
(*                                                                            *)
(* This file defines for each structure (SemiRing, Dioid, etc...) its type,   *)
(* its packers and its canonical properties:                                  *)
(*                                                                            *)
(*   * SemiRing (non commutative semi-rings):                                 *)
(*         SemiRing.type == interface type for semi-ring structure            *)
(* SemiRing_of_WrapChoice.Build T addA addC add0l mulA mul1l mul1r mulDl      *)
(*     mulDr mul0l mul0r == builds a SemiRing structure from the algebraic    *)
(*                          properties of its operations.                     *)
(*                          The carrier type T must have a WrapChoice         *)
(*                          canonical structure (see HB_wrappers.v).          *)
(*                     0 == the zero element (aditive identity)               *)
(*                     1 == the unit element (multiplicative identity)        *)
(*                 x + y == the addition of x and y in a semiRing             *)
(*                 x * y == the multiplication of x and y in a semiRing       *)
(*         addd_closed S <-> collective predicate S is closed under           *)
(*                          finite sums (0 and x + y in S, for x, y in S)     *)
(*         muld_closed S <-> collective predicate S is closed under finite    *)
(*                          multiplication (0 and x * y in S, for x, y in S)  *)
(*     semiring_closed S <-> collective predicate S is closed under finite    *)
(*                          addition and multiplication. This property        *)
(*                          coerces to addd_closed and muld_closed.           *)
(*          AddPred addS == packs addS : addd_closed S into an addPred S      *)
(*                          interface structure associating this property to  *)
(*                          the canonical pred_key S, i.e the k for wich S    *)
(*                          has a Canonical keyed_pred k structure.           *)
(*                          (see file ssrbool.v)                              *)
(*          MulPred mulS == packs mulS : muld_closed S into a mulPred S       *)
(*                          interface structure associating this property to  *)
(*                          the canonical pred_key S                          *)
(*     SemiRingPred mulS == packs mulS : muld_closed S into a semiringPred S  *)
(*                          interface structure associating the               *)
(*                          semiring_closed property to the canonical         *)
(*                          pred_key S (see above), wich must already be an   *)
(*                          AddPred.                                          *)
(* [SemiRing of U by <:] == semiRingType mixin for a subType whose base type  *)
(*                          is a semiRingType and whose predicate's canonical *)
(*                          pred_key is a semiRingPred.                       *)
(*                                                                            *)
(*   * ComSemiRing (multiplication is commutative):                           *)
(*      ComSemiRing.type == interface type for commutative semi ring          *)
(*                          structure                                         *)
(* ComSemiRing_of_SemiRing.Build R mulC                                       *)
(*                       == packs mulC into a comSemiRing; the carrier type R *)
(*                          must have a SemiRing canonical structure.         *)
(* ComSemiRing_of_WrapChoice.Build T addA addC add0l mulA mulC mul1l mulDl    *)
(*                 mul0l == builds a ComSemiRing structure using the          *)
(*                          commutativity to reduce the number of proof       *)
(*                          obligations.                                      *)
(*                          The carrier type T must have a WrapChoice         *)
(*                          canonical structure (see HB_wrappers.v).          *)
(* [ComSemiRing of R by <:] == commutativity mixin axiom for R when it is a   *)
(*                          subType of a commutative semi-ring.               *)
(*                                                                            *)
(*   * Dioid (idempotent semi-rings):                                         *)
(*            Dioid.type == interface type for dioid structure.               *)
(* Dioid_of_SemiRing_and_WrapPOrder.build D addxx le_def                      *)
(*                       == packs addxx into a Dioid; the carrier type R must *)
(*                          have both a SemiRing and a WrapPOrder canonical   *)
(*                          structure.                                        *)
(* Dioid_of_WrapPOrder.Build D addA addC add0l addxx mulA mul1l mul1r mulDl   *)
(*   mulDr mul0l mul0r addxx le_def                                           *)
(*                       == build a Dioid structure from the algebraic        *)
(*                          properties of its operations.                     *)
(*                          The carrier type T must have a WrapPOrder         *)
(*                          canonical structure (see HB_wrappers.v).          *)
(* Dioid_of_WrapChoice.Build D addA addC add0l addxx mulA mul1l mul1r mulDl   *)
(*   mulDr mul0l mul0r addxx == build a Dioid structure from the algebraic    *)
(*                          properties of its operations.                     *)
(*                          The carrier type T must have a WrapChoice         *)
(*                          canonical structure (see HB_wrappers.v).          *)
(*    [Dioid of R by <:] == idempotent mixin axiom for R when it is a         *)
(*                          subType of a dioid.                               *)
(*                                                                            *)
(*   * ComDioid:                                                              *)
(*         ComDioid.yype == interface type for commutative dioid structure    *)
(* ComDioid_of_Dioid.Build D mulC == packs mulC into a ComDioidType; the      *)
(*                          carrier type D must have a Dioid canonical        *)
(*                          structure.                                        *)
(* ComDioid_of_ComSemiRing_and_WrapPOrder.Build D addxx le_def                *)
(*                       == packs addxx into a ComDioid; the carrier type D   *)
(*                          must have both a Dioid and a WrapPOrder canonical *)
(*                          structure.                                        *)
(* ComDioid_of_WrapPOrder.Build D addA addC add0l addxx mulA mulC mul1l mulDl *)
(*          mul0l le_def == builds a ComDioid structure using the             *)
(*                          commutativity to reduce the number of proof       *)
(*                          obligations.                                      *)
(*                          The carrier type T must have a WrapPOrder         *)
(*                          canonical structure (see HB_wrappers.v).          *)
(* ComDioid_of_WrapChoice.Build D addA addC add0l addxx mulA mulC mul1l mulDl *)
(*                 mul0l == builds a ComDioid structure using the             *)
(*                          commutativity to reduce the number of proof       *)
(*                          obligations.                                      *)
(*                          The carrier type T must have a WrapChoice         *)
(*                          canonical structure (see HB_wrappers.v).          *)
(* [ComDioid of D by <:] == commutativity mixin axiom for S when it is a      *)
(*                          subType of a commutative dioid.                   *)
(*                                                                            *)
(* --> After declaring an instance of (Com)Dioid on T using                   *)
(*     (Com)Dioid_of_WrapChoice.Build the new porderType instance must be     *)
(*     made canonical by hand:                                                *)
(*     <<                                                                     *)
(*     Canonical T_porderType := [porderType of T for T_is_a_WrapPOrder].     *)
(*     >>                                                                     *)
(*   Notations are defined in scope dioid_scope (delimiter %D).               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope dioid_scope.
Delimit Scope dioid_scope with D.
Local Open Scope dioid_scope.

Import Order.Theory.

HB.mixin Record SemiRing_of_WrapChoice R of WrapChoice R := {
  zero : R;
  one : R;
  add : R -> R -> R;
  mul : R -> R -> R;
  adddA : associative add;
  adddC : commutative add;
  add0d : left_id zero add;
  muldA : associative mul;
  mul1d : left_id one mul;
  muld1 : right_id one mul;
  muldDl : left_distributive mul add;
  muldDr : right_distributive mul add;
  mul0d : left_zero zero mul;
  muld0 : right_zero zero mul;
}.

HB.structure Definition SemiRing :=
  { R of WrapChoice R & SemiRing_of_WrapChoice R }.

Coercion SemiRing_to_Equality (T : SemiRing.type) :=
  Eval hnf in [eqType of T for T].
Canonical SemiRing_to_Equality.
Coercion SemiRing_to_Choice (T : SemiRing.type) :=
  Eval hnf in [choiceType of T for T].
Canonical SemiRing_to_Choice.

Section SemiRingTheory.

Variables R : SemiRing.type.

Lemma addd0 : right_id (@zero R) add.
Proof. by move=> x; rewrite adddC add0d. Qed.

Canonical add_monoid := Monoid.Law adddA add0d addd0.
Canonical add_comoid := Monoid.ComLaw adddC.
Canonical mul_monoid := @Monoid.Law R _ _ muldA mul1d muld1.
Canonical muloid := @Monoid.MulLaw R _ _ mul0d muld0.
Canonical addoid := Monoid.AddLaw muldDl muldDr.

Local Notation "0" := zero : dioid_scope.
Local Notation "1" := one : dioid_scope.
Local Notation "+%D" := (@add _) : dioid_scope.
Local Infix "+" := (@add _) : dioid_scope.
Local Infix "*" := (@mul _) : dioid_scope.

Lemma adddAC : right_commutative (S := R) +%D.
Proof. by move=> x y z; rewrite -adddA (adddC y) adddA. Qed.

Lemma adddCA : left_commutative (S := R) +%D.
Proof. by move=> x y z; rewrite adddC -adddA (adddC x). Qed.

Lemma adddACA : interchange (S := R) +%D +%D.
Proof. by move=> a b c d; rewrite adddAC adddA -adddA (adddC d). Qed.

Section ClosedPredicates.

Variable S : predPredType R.

Definition addd_closed := 0 \in S /\ {in S &, forall u v, u + v \in S}.
Definition muld_closed := 1 \in S /\ {in S &, forall u v, u * v \in S}.
Definition semiring_closed := addd_closed /\ muld_closed.

Lemma semiring_closedA : semiring_closed -> addd_closed.
Proof. by case. Qed.
Lemma semiring_closedM : semiring_closed -> muld_closed.
Proof. by case. Qed.

End ClosedPredicates.

End SemiRingTheory.

HB.mixin Record ComSemiRing_of_SemiRing R of SemiRing R := {
  muldC : @commutative R _ mul;
}.

HB.structure Definition ComSemiRing :=
  { R of ComSemiRing_of_SemiRing R & SemiRing R }.

HB.factory Record ComSemiRing_of_WrapChoice R of WrapChoice R := {
  zero : R;
  one : R;
  add : R -> R -> R;
  mul : R -> R -> R;
  adddA : associative add;
  adddC : commutative add;
  add0d : left_id zero add;
  muldA : associative mul;
  muldC : commutative mul;
  mul1d : left_id one mul;
  muldDl : left_distributive mul add;
  mul0d : left_zero zero mul;
}.

HB.builders Context R (f : ComSemiRing_of_WrapChoice R).

  Lemma muld1 : right_id one mul.
  Proof. by move=> x; rewrite muldC mul1d. Qed.

  Lemma muldDr : right_distributive mul add.
  Proof. by move=> x y z; rewrite muldC muldDl !(muldC x). Qed.

  Lemma muld0 : right_zero zero mul.
  Proof. by move=> x; rewrite muldC mul0d. Qed.

  HB.instance Definition to_SemiRing_of_WrapChoice :=
    SemiRing_of_WrapChoice.Build
      R adddA adddC add0d
      muldA mul1d muld1 muldDl muldDr mul0d muld0.

  HB.instance Definition to_ComSemiRing_of_SemiRing :=
    ComSemiRing_of_SemiRing.Build R muldC.

HB.end.

Coercion ComSemiRing_to_Equality (T : ComSemiRing.type) :=
  Eval hnf in [eqType of T for T].
Canonical ComSemiRing_to_Equality.
Coercion ComSemiRing_to_Choice (T : ComSemiRing.type) :=
  Eval hnf in [choiceType of T for T].
Canonical ComSemiRing_to_Choice.

Section ComSemiRingTheory.

Variables R : ComSemiRing.type.

Local Notation "*%D" := (@mul _) : dioid_scope.
Local Infix "*" := (@mul _) : dioid_scope.

Lemma muldAC : right_commutative (S := R) *%D.
Proof. by move=> x y z; rewrite -muldA (muldC y) muldA. Qed.

Lemma muldCA : left_commutative (S := R) *%D.
Proof. by move=> x y z; rewrite muldC -muldA (muldC x). Qed.

Lemma muldACA : interchange (S := R) *%D *%D.
Proof. by move=> a b c d; rewrite muldAC muldA -muldA (muldC d). Qed.

End ComSemiRingTheory.

HB.mixin Record Dioid_of_SemiRing_and_WrapPOrder D
         of SemiRing D & WrapPOrder D := {
  adddd : @idempotent D add;
  le_def : forall (a b : D),
      (Order.POrder.le wrap_porderMixin a b)
      = (Equality.op wrap_eqMixin (add a b) b);
}.

HB.structure Definition Dioid :=
  { D of Dioid_of_SemiRing_and_WrapPOrder D & SemiRing D & WrapPOrder D }.

HB.factory Record Dioid_of_WrapPOrder D of WrapPOrder D := {
  zero : D;
  one : D;
  add : D -> D -> D;
  mul : D -> D -> D;
  adddA : associative add;
  adddC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  muldA : associative mul;
  mul1d : left_id one mul;
  muld1 : right_id one mul;
  muldDl : left_distributive mul add;
  muldDr : right_distributive mul add;
  mul0d : left_zero zero mul;
  muld0 : right_zero zero mul;
  le_def : forall (a b : D),
      (Order.POrder.le wrap_porderMixin a b)
      = (Equality.op wrap_eqMixin (add a b) b);
}.

HB.builders Context D (f : Dioid_of_WrapPOrder D).

  HB.instance Definition to_SemiRing_of_WrapChoice :=
    SemiRing_of_WrapChoice.Build
      D adddA adddC add0d
      muldA mul1d muld1 muldDl muldDr mul0d muld0.

  HB.instance Definition to_Dioid_of_SemiRing_and_WrapPOrder :=
    Dioid_of_SemiRing_and_WrapPOrder.Build D adddd le_def.

HB.end.

HB.factory Record Dioid_of_WrapChoice D of WrapChoice D := {
  zero : D;
  one : D;
  add : D -> D -> D;
  mul : D -> D -> D;
  adddA : associative add;
  adddC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  muldA : associative mul;
  mul1d : left_id one mul;
  muld1 : right_id one mul;
  muldDl : left_distributive mul add;
  muldDr : right_distributive mul add;
  mul0d : left_zero zero mul;
  muld0 : right_zero zero mul;
}.

HB.builders Context D (f : Dioid_of_WrapChoice D).

  HB.instance Definition to_SemiRing_of_WrapChoice :=
    SemiRing_of_WrapChoice.Build
      D adddA adddC add0d
      muldA mul1d muld1 muldDl muldDr mul0d muld0.

  Canonical D_is_a_eqType := [eqType of D for D_is_a_WrapChoice].

  Definition le_dioid a b := add a b == b.

  Definition lt_dioid a b := (b != a) && le_dioid a b.

  Lemma lt_def_dioid a b : lt_dioid a b = (b != a) && le_dioid a b.
  Proof. by []. Qed.

  Lemma le_refl_dioid : reflexive le_dioid.
  Proof. by move=> a; rewrite /le_dioid adddd. Qed.

  Lemma le_anti_dioid : antisymmetric le_dioid.
  Proof.
  by move=> a b /andP[]; rewrite /le => /eqP ? /eqP; rewrite adddC => <-.
  Qed.

  Lemma le_trans_dioid : transitive le_dioid.
  Proof.
  move=> a b c; rewrite /le_dioid => /eqP H /eqP <-.
  by rewrite -[in X in _ == X]H adddA.
  Qed.

  Definition dioid_porderMixin :=
    LePOrderMixin lt_def_dioid le_refl_dioid le_anti_dioid le_trans_dioid.

  HB.instance Definition to_WrapPOrder_of_WrapChoice :=
    WrapPOrder_of_WrapChoice.Build D dioid_porderMixin.

  Lemma le_def (a b : D) :
    Order.POrder.le wrap_porderMixin a b =
    Equality.op wrap_eqMixin (SemiRing.Exports.add a b) b.
  Proof. by []. Qed.

  HB.instance Definition to_Dioid_of_SemiRing_and_WrapPOrder :=
    Dioid_of_SemiRing_and_WrapPOrder.Build D adddd le_def.

HB.end.

Coercion Dioid_to_Equality (T : Dioid.type) :=
  Eval hnf in [eqType of T for T].
Canonical Dioid_to_Equality.
Coercion Dioid_to_Choice (T : Dioid.type) :=
  Eval hnf in [choiceType of T for T].
Canonical Dioid_to_Choice.
Coercion Dioid_to_POrder (T : Dioid.type) :=
  Eval hnf in [porderType of T for T].
Canonical Dioid_to_POrder.

Section DioidTheory.

Variables D : Dioid.type.

Implicit Type a b c : D.

Local Notation "0" := zero : dioid_scope.
Local Notation "1" := one : dioid_scope.
Local Notation "+%D" := (@add _) : dioid_scope.
Local Notation "*%D" := (@mul _) : dioid_scope.
Local Infix "+" := (@add _) : dioid_scope.
Local Infix "*" := (@mul _) : dioid_scope.
Local Infix "<=" := (@Order.le _ _) : dioid_scope.
Local Notation "a <= b :> T" := ((a : T) <= (b : T)) (only parsing) : dioid_scope.

Lemma le_def a b : (a <= b) = (a + b == b).
Proof. by rewrite /Order.le le_def. Qed.

Lemma le0d a : 0 <= a :> D.
Proof. by rewrite le_def add0d. Qed.

Lemma led_add2r c : {homo +%D^~ c : a b / a <= b }.
Proof.
move => a b; rewrite !le_def => /eqP H.
by rewrite adddCA -adddA adddd adddA (adddC b) H.
Qed.

Lemma led_add2l c : {homo +%D c : a b / a <= b }.
Proof. move=> a b; rewrite !(adddC c); exact: led_add2r. Qed.

Lemma led_add a b c d : a <= c -> b <= d -> a + b <= c + d.
Proof. move=> Hac Hbd; exact/(le_trans (led_add2r _ Hac)) /led_add2l. Qed.

Lemma led_addl a b : a <= b + a.
Proof. by rewrite le_def adddCA adddd. Qed.

Lemma led_addr a b : a <= a + b.
Proof. by rewrite le_def adddA adddd. Qed.

Lemma led_add_eqv a b c :  (b + c <= a) = ((b <= a) && (c <= a)).
Proof.
apply/idP/idP => [Ha | /andP[]].
- apply/andP; split.
  + exact/(le_trans _ Ha) /led_addr.
  + exact/(le_trans _ Ha) /led_addl.
- rewrite 2!le_def => /eqP <- /eqP <-.
  by rewrite adddCA adddA led_addr.
Qed.

Lemma led_mul2l c : {homo *%D c : a b / a <= b }.
Proof. by move=> a b; rewrite le_def => /eqP <-; rewrite muldDr led_addr. Qed.

Lemma led_mul2r c : {homo *%D^~ c : a b / a <= b }.
Proof. by move=> a b; rewrite le_def => /eqP <-; rewrite muldDl led_addr. Qed.

Lemma led_mul a b c d : a <= c -> b <= d -> a * b <= c * d.
Proof. move=> Hac Hbd; exact/(le_trans (led_mul2r _ Hac)) /led_mul2l. Qed.

End DioidTheory.

HB.structure Definition ComDioid :=
  { D of ComSemiRing_of_SemiRing D & Dioid D }.

HB.factory Record ComDioid_of_WrapPOrder D of WrapPOrder D := {
  zero : D;
  one : D;
  add : D -> D -> D;
  mul : D -> D -> D;
  adddA : associative add;
  adddC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  muldA : associative mul;
  muldC : commutative mul;
  mul1d : left_id one mul;
  muldDl : left_distributive mul add;
  mul0d : left_zero zero mul;
  le_def : forall (a b : D),
      (Order.POrder.le wrap_porderMixin a b)
      = (Equality.op wrap_eqMixin (add a b) b);
}.

HB.builders Context D (f : ComDioid_of_WrapPOrder D).

  Lemma muld1 : right_id one mul.
  Proof. by move=> x; rewrite muldC mul1d. Qed.

  Lemma muldDr : right_distributive mul add.
  Proof.
  Proof. by move=> x y z; rewrite muldC muldDl !(muldC x). Qed.

  Lemma muld0 : right_zero zero mul.
  Proof. by move=> x; rewrite muldC mul0d. Qed.

  HB.instance Definition to_Dioid_of_WrapPOrder :=
    Dioid_of_WrapPOrder.Build
      D adddA adddC add0d adddd
      muldA mul1d muld1 muldDl muldDr mul0d muld0 le_def.

  HB.instance Definition to_ComDioid_of_Dioid :=
    ComSemiRing_of_SemiRing.Build D muldC.

HB.end.

HB.factory Record ComDioid_of_WrapChoice D of WrapChoice D := {
  zero : D;
  one : D;
  add : D -> D -> D;
  mul : D -> D -> D;
  adddA : associative add;
  adddC : commutative add;
  add0d : left_id zero add;
  adddd : idempotent add;
  muldA : associative mul;
  muldC : commutative mul;
  mul1d : left_id one mul;
  muldDl : left_distributive mul add;
  mul0d : left_zero zero mul;
}.

HB.builders Context D (f : ComDioid_of_WrapChoice D).

  Lemma muld1 : right_id one mul.
  Proof. by move=> x; rewrite muldC mul1d. Qed.

  Lemma muldDr : right_distributive mul add.
  Proof.
  Proof. by move=> x y z; rewrite muldC muldDl !(muldC x). Qed.

  Lemma muld0 : right_zero zero mul.
  Proof. by move=> x; rewrite muldC mul0d. Qed.

  HB.instance Definition to_Dioid_of_WrapChoice :=
    Dioid_of_WrapChoice.Build
      D adddA adddC add0d adddd
      muldA mul1d muld1 muldDl muldDr mul0d muld0.

  HB.instance Definition to_ComDioid_of_Dioid :=
    ComSemiRing_of_SemiRing.Build D muldC.

HB.end.

Coercion ComDioid_to_Equality (T : ComDioid.type) :=
  Eval hnf in [eqType of T for T].
Canonical ComDioid_to_Equality.
Coercion ComDioid_to_Choice (T : ComDioid.type) :=
  Eval hnf in [choiceType of T for T].
Canonical ComDioid_to_Choice.
Coercion ComDioid_to_POrder (T : ComDioid.type) :=
  Eval hnf in [porderType of T for T].
Canonical ComDioid_to_POrder.

(* Interface structures for algebraically closed predicates. *)
Module Pred.

Structure add V S := Add {add_key : pred_key S; _ : @addd_closed V S}.
Structure mul R S := Mul {mul_key : pred_key S; _ : @muld_closed R S}.
Structure semiring R S :=
  SemiRing {semiring_add : add S; _ : @muld_closed R S}.

Section Subtyping.

Fact semiring_mulr R S : @semiring R S -> muld_closed S.
Proof. by case. Qed.

Definition semiring_mul R S (ringS : @semiring R S) :=
  Mul (add_key (semiring_add ringS)) (semiring_mulr ringS).

End Subtyping.

Section Extensionality.
(* This could be avoided by exploiting the Coq 8.4 eta-convertibility.        *)

Lemma add_ext (U : SemiRing.type) S k (kS : @keyed_pred U S k) :
  addd_closed kS -> addd_closed S.
Proof.
by case=> S0 addS; split=> [|x y]; rewrite -!(keyed_predE kS) //; apply: addS.
Qed.

Lemma mul_ext (R : SemiRing.type) S k (kS : @keyed_pred R S k) :
  muld_closed kS -> muld_closed S.
Proof.
by case=> S1 mulS; split=> [|x y]; rewrite -!(keyed_predE kS) //; apply: mulS.
Qed.

End Extensionality.

Module Exports.

Notation addd_closed := addd_closed.
Notation muld_closed := muld_closed.
Notation semiring_closed := semiring_closed.

Coercion semiring_closedA : semiring_closed >-> addd_closed.
Coercion semiring_closedM : semiring_closed >-> muld_closed.
Coercion add_key : add >-> pred_key.
Coercion mul_key : mul >-> pred_key.
Coercion semiring_add : semiring >-> add.
Coercion semiring_mul : semiring >-> mul.
Canonical semiring_mul.

Notation addPred := add.
Notation mulPred := mul.
Notation semiringPred := semiring.

Definition AddPred U S k kS DkS := Add k (@add_ext U S k kS DkS).
Definition MulPred R S k kS MkS := Mul k (@mul_ext R S k kS MkS).
Definition SemiRingPred R S k kS MkS := SemiRing k (@mul_ext R S k kS MkS).

End Exports.

End Pred.
Import Pred.Exports.

Section SemiRingPred.

Variables (V : SemiRing.type) (S : predPredType V).

Section Add.

Variables (addS : addPred S) (kS : keyed_pred addS).

Lemma rpred0D : addd_closed kS.
Proof. split=> [|x y]; rewrite !keyed_predE; case: addS=> _ [_]//; exact. Qed.

Lemma rpred0 : (@zero V) \in kS.
Proof. by case: rpred0D. Qed.

Lemma rpredD : {in kS &, forall u v, (@add V u v) \in kS}.
Proof. by case: rpred0D. Qed.

End Add.

Section Mul.

Variables (mulS : mulPred S) (kS : keyed_pred mulS).

Lemma rpred1M : muld_closed kS.
Proof.
split=> [ | x y]; rewrite !keyed_predE; case: mulS => _ [_] //; exact.
Qed.

Lemma rpred1 : (@one V) \in kS.
Proof. by case: rpred1M. Qed.

Lemma rpredM : {in kS &, forall u v, (@mul V u v) \in kS}.
Proof. by case: rpred1M. Qed.

End Mul.

End SemiRingPred.

Module SubType.

Section SemiRing.

Variables (V : SemiRing.type) (S : predPredType V).
Variables (subS : semiringPred S) (kS : keyed_pred subS).
Variable U : subType (mem kS).

Let inU v Sv : U := Sub v Sv.
Let zeroU := inU (rpred0 kS).
Let oneU := inU (rpred1 kS).
Let addU (u1 u2 : U) := inU (rpredD (valP u1) (valP u2)).
Let mulU (u1 u2 : U) := inU (rpredM (valP u1) (valP u2)).

Fact adddA : associative addU.
Proof. by move=> a b c; apply: val_inj; rewrite !SubK adddA. Qed.

Fact adddC : commutative addU.
Proof. by move=> a b; apply: val_inj; rewrite !SubK adddC. Qed.

Fact add0d : left_id zeroU addU.
Proof. by move=> a; apply: val_inj; rewrite !SubK add0d. Qed.

Fact muldA : associative mulU.
Proof. by move=> a b c; apply: val_inj; rewrite !SubK muldA. Qed.

Fact mul1d : left_id oneU mulU.
Proof. by move=> a; apply: val_inj; rewrite !SubK mul1d. Qed.

Fact muld1 : right_id oneU mulU.
Proof. by move=> a; apply: val_inj; rewrite !SubK muld1. Qed.

Fact muldDl : @left_distributive U U mulU addU.
Proof. by move=> a b c; apply: val_inj; rewrite !SubK muldDl. Qed.

Fact muldDr : right_distributive mulU addU.
Proof. by move=> a b c; apply: val_inj; rewrite !SubK muldDr. Qed.

Lemma mul0d : left_zero zeroU mulU.
Proof. by move=> a; apply: val_inj; rewrite !SubK mul0d. Qed.

Lemma muld0 : right_zero zeroU mulU.
Proof. by move=> a; apply: val_inj; rewrite !SubK muld0. Qed.

Definition semiRingMixin of phant U :=
  SemiRing_of_WrapChoice.Build
    _ adddA adddC add0d muldA mul1d muld1 muldDl muldDr mul0d muld0.

End SemiRing.

Lemma comSemiRingMixin (R : ComSemiRing.type) (T : SemiRing.type) (f : T -> R) :
phant T -> injective f -> {morph f : x y / mul x y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM muldC. Qed.

Lemma dioidMixin (R : Dioid.type) (T : SemiRing.type) (f : T -> R) :
phant T -> injective f -> {morph f : x y / add x y} -> @idempotent T add.
Proof. by move=> _ inj_f fM x; apply: inj_f; rewrite !fM adddd. Qed.

Lemma dioidMixin' (R : Dioid.type) (T : SemiRing.type) (f : T -> R)
  (_ : phant T) (eM : Equality.mixin_of T) (oM : @Order.POrder.mixin_of T eM) :
injective f -> {morph f : x y / add x y} ->
{mono f : x y / Equality.op eM x y >-> x == y} ->
{mono f : x y / Order.POrder.le oM x y >-> (x <= y)%O} ->
forall (a b : T), (Order.POrder.le oM a b) = (Equality.op eM (add a b) b).
Proof. by move=> inj_f fM fM' fM'' x y; rewrite -fM'' le_def -fM fM'. Qed.

Lemma comDioidMixin (R : ComDioid.type) (T : Dioid.type) (f : T -> R) :
phant T -> injective f -> {morph f : x y / mul x y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM muldC. Qed.

Module Exports.

Notation "[ 'SemiRing' 'of' U 'by' <: ]" := (semiRingMixin (Phant U))
  (at level 0, format "[ 'SemiRing' 'of' U 'by' <: ]") : form_scope.

Notation "[ 'ComSemiRing' 'of' R 'by' <: ]" :=
  (ComSemiRing_of_SemiRing.Build
     _ (comSemiRingMixin (Phant R) val_inj (rrefl _)))
  (at level 0, format "[ 'ComSemiRing' 'of' R 'by' <: ]") : form_scope.

Notation "[ 'Dioid' 'of' R 'by' <: ]" :=
  (Dioid_of_SemiRing_and_WrapPOrder.Build
     R%type (dioidMixin (Phant R) val_inj (rrefl _))
     (@dioidMixin' _ _ _ (Phant R) wrap_eqMixin wrap_porderMixin
                  val_inj (rrefl _) (rrefl _) (rrefl _)))
  (at level 0, format "[ 'Dioid' 'of' R 'by' <: ]") : form_scope.

Notation "[ 'ComDioid' 'of' R 'by' <: ]" :=
  (ComSemiRing_of_SemiRing.Build _ (comDioidMixin (Phant R) val_inj (rrefl _)))
  (at level 0, format "[ 'ComDioid' 'of' R 'by' <: ]") : form_scope.

End Exports.

End SubType.

Export Pred.Exports SubType.Exports.

Notation "0" := zero : dioid_scope.
Notation "1" := one : dioid_scope.
Notation "+%D" := (@add _) : dioid_scope.
Notation "*%D" := (@mul _) : dioid_scope.
Infix "+" := (@add _) : dioid_scope.
Infix "*" := (@mul _) : dioid_scope.

Notation led := (@Order.le dioid_display _) (only parsing).
Notation "@ 'led' R" :=
  (@Order.le dioid_display R) (at level 10, R at level 8, only parsing).
Notation ltd := (@Order.lt dioid_display _) (only parsing).
Notation "@ 'ltd' R" :=
  (@Order.lt dioid_display R) (at level 10, R at level 8, only parsing).
Notation ged := (@Order.ge dioid_display _) (only parsing).
Notation "@ 'ged' R" :=
  (@Order.ge dioid_display R) (at level 10, R at level 8, only parsing).
Notation gtd := (@Order.gt dioid_display _) (only parsing).
Notation "@ 'gtd' R" :=
  (@Order.gt dioid_display R) (at level 10, R at level 8, only parsing).

Notation "<=%D" := led : dioid_scope.
Notation ">=%D" := ged : dioid_scope.
Notation "<%D" := ltd : dioid_scope.
Notation ">%D" := gtd : dioid_scope.

Notation "<= b" := (ged b) : dioid_scope.
Notation "<= b :> T" := (<= (b : T)) (only parsing) : dioid_scope.
Notation ">= b" := (led b) : dioid_scope.
Notation ">= b :> T" := (>= (b : T)) (only parsing) : dioid_scope.

Notation "< b" := (gtd b) : dioid_scope.
Notation "< b :> T" := (< (b : T)) (only parsing) : dioid_scope.
Notation "> b" := (ltd b) : dioid_scope.
Notation "> b :> T" := (> (b : T)) (only parsing) : dioid_scope.

Notation "a <= b" := (led a b) : dioid_scope.
Notation "a <= b :> T" := ((a : T) <= (b : T)) (only parsing) : dioid_scope.
Notation "a >= b" := (b <= a) (only parsing) : dioid_scope.
Notation "a >= b :> T" := ((a : T) >= (b : T)) (only parsing) : dioid_scope.

Notation "a < b" := (ltd a b) : dioid_scope.
Notation "a < b :> T" := ((a : T) < (b : T)) (only parsing) : dioid_scope.
Notation "a > b" := (b < a) (only parsing) : dioid_scope.
Notation "a > b :> T" := ((a : T) > (b : T)) (only parsing) : dioid_scope.

Notation "a <= b <= c" := ((led a b) && (led b c)) : dioid_scope.
Notation "a < b <= c"  := ((ltd a b) && (led b c)) : dioid_scope.
Notation "a <= b < c"  := ((led a b) && (ltd b c)) : dioid_scope.
Notation "a < b < c"   := ((ltd a b) && (ltd b c)) : dioid_scope.
