From HB Require Import structures.
From Coq Require Import ZArith ssreflect ssrbool.
From mathcomp Require Import ssrfun eqtype choice order ssrnat bigop.
Require Import mathcomp.dioid.HB_wrappers mathcomp.dioid.dioid.

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

Lemma mulenC : commutative mulen.
Proof. by move=> [?||] [?||] //=; rewrite addnC. Qed.

Lemma mul1en : left_id eone mulen.
Proof. by case. Qed.

Lemma mulenDl : left_distributive mulen adden.
Proof. by move=> [?||] [?||] [?||] //=; rewrite addn_maxl. Qed.

Lemma mul0en : left_zero ezero mulen.
Proof. by case. Qed.

HB.instance Definition enat_WrapChoice_axioms :=
  WrapChoice_of_TYPE.Build enat enat_eqMixin enat_choiceMixin.
Canonical enat_eqType := [eqType of enat for enat_is_a_WrapChoice].
Canonical enat_choiceType := [choiceType of enat for enat_is_a_WrapChoice].

HB.instance Definition enat_ComDioid_axioms :=
  ComDioid_of_WrapChoice.Build
    enat addenA addenC add0en addenen mulenA mulenC mul1en mulenDl mul0en.
Canonical enat_porderType := [porderType of enat for enat_is_a_WrapPOrder].

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

Require Import mathcomp.analysis.classical_sets.
Require Import mathcomp.dioid.complete_lattice.
Require Import mathcomp.dioid.complete_dioid.

Parameter set_joinen : set enat -> enat.

Axiom set_joinen_is_lub : set_f_is_lub wrap_porderMixin set_joinen.

HB.instance Definition enat_CompleteLattice_axioms :=
  CompleteLattice_of_WrapPOrder.Build enat set_joinen_is_lub.
Canonical enat_latticeType := [latticeType of enat for enat_is_a_WrapLattice].

Axiom set_mulenDl : forall (a : enat) (B : set enat),
  (a * set_join B = set_join [set a * x | x in B])%D.

Axiom set_mulenDr : forall (a : enat) (B : set enat),
  (set_join B * a = set_join [set x * a | x in B])%D.

HB.instance Definition enat_CompleteDioid_axioms :=
  CompleteDioid_of_Dioid_and_CompleteLattice.Build enat set_mulenDl set_mulenDr.
