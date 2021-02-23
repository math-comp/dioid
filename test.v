From HB Require Import structures.
From Coq Require Import ZArith ssreflect ssrbool.
From mathcomp Require Import ssrfun eqtype choice order ssrnat bigop.
Require Import mathcomp.dioid.dioid.

(** nat extended with -oo and +oo *)
Variant enat := ENFin of nat | ENPInf | ENMInf.

Definition eq_enat (x y : enat) :=
  match x, y with
  | ENFin x, ENFin y => x == y
  | ENPInf, ENPInf => true
  | ENMInf, ENMInf => true
  | _, _ => false
  end.

Lemma enat_eqP : Equality.axiom eq_enat.
Proof. by case=> [?||][?||]; apply: (iffP idP) => //= [/eqP|[]] ->. Qed.

Definition enat_eqMixin := Equality.Mixin enat_eqP.

Definition code (x : enat) :=
  match x with
  | ENFin x => GenTree.Node 0 (GenTree.Leaf x :: nil)
  | ENPInf => GenTree.Node 1 nil
  | ENMInf => GenTree.Node 2 nil
  end.

Definition decode (x : GenTree.tree nat) : option enat :=
  match x with
  | GenTree.Node 0 (GenTree.Leaf x :: nil) => Some (ENFin x)
  | GenTree.Node 1 nil => Some ENPInf
  | GenTree.Node 2 nil => Some ENMInf
  | _ => None
  end.

Lemma codeK : pcancel code decode. Proof. by case. Qed.

Definition enat_choiceMixin := PcanChoiceMixin codeK.

Definition ezero := ENMInf.
Definition eone := ENFin 0.
Definition adden (x y : enat) :=
  match x, y with
  | ENFin x, ENFin y => ENFin (maxn x y)
  | ENPInf, _ | _, ENPInf => ENPInf
  | ENMInf, x | x, ENMInf => x
  end.
Definition mulen (x y : enat) :=
  match x, y with
  | ENFin x, ENFin y => ENFin (x + y)
  | ENMInf, _ | _, ENMInf => ENMInf
  | ENPInf, _ | _, ENPInf => ENPInf
  end.

Lemma addenA : associative adden.
Proof. by move=> [?||] [?||] [?||] //=; rewrite maxnA. Qed.

Lemma addenC : commutative adden.
Proof. by move=> [?||] [?||] //=; rewrite maxnC. Qed.

Lemma add0en : left_id ezero adden.
Proof. by case. Qed.

Lemma addenen : idempotent adden.
Proof. by move=> [?||] //=; rewrite maxnn. Qed.

Lemma mulenA : associative mulen.
Proof. by move=> [?||] [?||] [?||] //=; rewrite addnA. Qed.

Lemma mul1en : left_id eone mulen.
Proof. by case. Qed.

Lemma mulen1 : right_id eone mulen.
Proof. by move=> [?||] //=; rewrite addn0. Qed.

Lemma mulenDl : left_distributive mulen adden.
Proof. by move=> [?||] [?||] [?||] //=; rewrite addn_maxl. Qed.

Lemma mulenDr : right_distributive mulen adden.
Proof. by move=> [?||] [?||] [?||] //=; rewrite addn_maxr. Qed.

Lemma mul0en : left_zero ezero mulen.
Proof. by case. Qed.

Lemma mulen0 : right_zero ezero mulen.
Proof. by case. Qed.

Definition enat_dioid_axioms :=
  Dioid_of_TYPE.Build
    enat enat_eqMixin enat_choiceMixin
    addenA addenC add0en addenen
    mulenA mul1en mulen1 mulenDl mulenDr mul0en mulen0.

HB.instance enat enat_dioid_axioms.
Fail Check @eq_op _ ezero ezero.
Check @eq_op (dioid_eqType _) ezero ezero.
Canonical enat_eqType := [eqType of enat for enat_is_a_SemiRing].
Canonical enat_choiceType := [choiceType of enat for enat_is_a_SemiRing].
Canonical enat_porderType := [porderType of enat for enat_is_a_Dioid].

Check @eq_op _ ezero ezero.
Check @eq_op (dioid_eqType _) ezero ezero.

Check (eone == ezero).

Check (ezero <= ezero)%D.

Goal (\big[+%D/0%D]_(0 <= i < 2) (ENFin 42)
      = (\big[+%D/0%D]_(0 <= i < 1) (ENFin 42)) + (ENFin 42))%D.
Proof. by rewrite big_nat_recr. Qed.

Goal (ENFin 42 <= ENFin 12 + ENFin 42)%D.
Proof.
rewrite adddC.
exact: led_addr.
Qed.
