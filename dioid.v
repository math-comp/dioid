From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat bigop.

(** To declare an instance of SemiRing on R:
  <<
  From HB Require Import structures.

  Definition R_semiring_axioms :=
    SemiRing_of_TYPE.Build
      R R_eqMixin R_choiceMixin
      addA addC add0r addenen mulA mul1r mulr1 mulDl mulDr mul0r mulr0.

  HB.instance R R_semiring_axioms.
  Canonical R_eqType := [eqType of R for R_is_a_SemiRing].
  Canonical R_choiceType := [choiceType of R for R_is_a_SemiRing].
  >>
  Similarly, after declaring an instance of Dioid:
  <<
  Canonical R_porderType := [porderType of R for R_is_a_Dioid].
  >>
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope dioid_scope.
Delimit Scope dioid_scope with D.
Local Open Scope dioid_scope.

Import Order.Theory.

HB.mixin Record SemiRing_of_TYPE R := {
  semiRing_eqMixin : Equality.mixin_of R;
  semiRing_choiceMixin : Choice.mixin_of R;
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

HB.structure Definition SemiRing := { R of SemiRing_of_TYPE R }.

Section SemiRingTheory.

Variables R : SemiRing.type.

Canonical semiRing_eqType := EqType R semiRing_eqMixin.
Canonical semiRing_choiceType := ChoiceType R semiRing_choiceMixin.

Lemma addd0 : right_id (@zero R) add.
Proof. by move=> x; rewrite adddC add0d. Qed.

Canonical add_monoid := Monoid.Law adddA add0d addd0.
Canonical add_comoid := Monoid.ComLaw adddC.
Canonical mul_monoid := @Monoid.Law R _ _ muldA mul1d muld1.
Canonical muloid := @Monoid.MulLaw R _ _ mul0d muld0.
Canonical addoid := Monoid.AddLaw muldDl muldDr.

Local Notation "+%D" := (@add _) : dioid_scope.
Local Infix "+" := (@add _) : dioid_scope.

Lemma adddAC : right_commutative (S := R) +%D.
Proof. by move=> x y z; rewrite -adddA (adddC y) adddA. Qed.

Lemma adddCA : left_commutative (S := R) +%D.
Proof. by move=> x y z; rewrite adddC -adddA (adddC x). Qed.

Lemma adddACA : interchange (S := R) +%D +%D.
Proof. by move=> a b c d; rewrite adddAC adddA -adddA (adddC d). Qed.

End SemiRingTheory.
Coercion semiRing_eqType : SemiRing.type >-> eqType.
Coercion semiRing_choiceType : SemiRing.type >-> choiceType.

HB.mixin Record Dioid_of_SemiRing R of SemiRing R := {
  adddd : @idempotent R add;
}.

HB.factory Record Dioid_of_TYPE D := {
  dioid_eqMixin : Equality.mixin_of D;
  dioid_choiceMixin : Choice.mixin_of D;
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

HB.builders Context D (a : Dioid_of_TYPE D).

  HB.instance Definition to_SemiRing_of_TYPE :=
    SemiRing_of_TYPE.Build
      D dioid_eqMixin dioid_choiceMixin
      adddA adddC add0d
      muldA mul1d muld1 muldDl muldDr mul0d muld0.

  HB.instance Definition to_Dioid_of_SemiRing :=
    Dioid_of_SemiRing.Build D adddd.

HB.end.

HB.structure Definition Dioid := { D of Dioid_of_TYPE D }.

Section DioidTheory.

Variables D : Dioid.type.

Implicit Type a b c : D.

Canonical dioid_eqType := EqType D semiRing_eqMixin.
Canonical dioid_choiceType := ChoiceType D semiRing_choiceMixin.

Local Notation "0" := zero : dioid_scope.
Local Notation "1" := one : dioid_scope.
Local Notation "+%D" := (@add _) : dioid_scope.
Local Notation "*%D" := (@mul _) : dioid_scope.
Local Infix "+" := (@add _) : dioid_scope.
Local Infix "*" := (@mul _) : dioid_scope.

Definition le_dioid a b := a + b == b.

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

Fact dioid_display : unit. Proof. by []. Qed.

Definition dioid_porderMixin :=
  LePOrderMixin lt_def_dioid le_refl_dioid le_anti_dioid le_trans_dioid.

Canonical dioid_porderType :=
  POrderType dioid_display D dioid_porderMixin.

Local Notation "a <= b" := (@Order.le _ [porderType of D] a b) : dioid_scope.

Lemma le0d a : 0 <= a :> D.
Proof. by rewrite le_def add0d. Qed.

Lemma led_add2r c : {homo +%D^~ c : a b / a <= b }.
Proof.
move => a b /eqP H; apply/eqP.
by rewrite adddCA -adddA adddd adddA (adddC b) H.
Qed.

Lemma led_add2l c : {homo +%D c : a b / a <= b }.
Proof. move=> a b; rewrite !(adddC c); exact: led_add2r. Qed.

Lemma led_add a b c d : a <= c -> b <= d -> a + b <= c + d.
Proof. move=> Hac Hbd; exact/(le_trans (led_add2r _ Hac)) /led_add2l. Qed.

Lemma led_addl a b : a <= b + a.
Proof. by apply/eqP; rewrite adddCA adddd. Qed.

Lemma led_addr a b : a <= a + b.
Proof. by apply/eqP; rewrite adddA adddd. Qed.

Lemma led_add_eqv a b c :  (b + c <= a) = ((b <= a) && (c <= a)).
Proof.
apply/idP/idP => [Ha | /andP[/eqP <- /eqP <-]].
- apply/andP; split.
  + exact/(le_trans _ Ha) /led_addr.
  + exact/(le_trans _ Ha) /led_addl.
- by rewrite adddCA adddA led_addr.
Qed.

Lemma led_mul2l c : {homo *%D c : a b / a <= b }.
Proof. by move=> a b /eqP Hb; apply/eqP; rewrite -muldDr Hb. Qed.

Lemma led_mul2r c : {homo *%D^~ c : a b / a <= b }.
Proof. by move=> a b /eqP Hb; apply/eqP; rewrite -muldDl Hb. Qed.

Lemma led_mul a b c d : a <= c -> b <= d -> a * b <= c * d.
Proof. move=> Hac Hbd; exact/(le_trans (led_mul2r _ Hac)) /led_mul2l. Qed.

End DioidTheory.
Coercion dioid_eqType : Dioid.type >-> eqType.
Coercion dioid_choiceType : Dioid.type >-> choiceType.
Coercion dioid_porderType : Dioid.type >-> porderType.

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
