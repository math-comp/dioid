From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import fintype ssrnat bigop.
Require Import mathcomp.analysis.classical_sets.
Require Import HB_wrappers dioid complete_lattice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope dioid_scope.

Import Order.Theory.

HB.mixin Record CompleteDioid_of_Dioid_and_CompleteLattice D
         of Dioid D & CompleteLattice D := {
  set_mulDl : forall (a : D) (B : set D),
      a * set_join B = set_join [set a * x | x in B]%classic;
  set_mulDr : forall (a : D) (B : set D),
      set_join B * a = set_join [set x * a | x in B]%classic;
}.

HB.structure Definition CompleteDioid :=
  { D of Dioid D & CompleteLattice D
    & CompleteDioid_of_Dioid_and_CompleteLattice D }.

Coercion CompleteDioid_to_Equality (T : CompleteDioid.type) :=
  Eval hnf in [eqType of T for T].
Canonical CompleteDioid_to_Equality.
Coercion CompleteDioid_to_Choice (T : CompleteDioid.type) :=
  Eval hnf in [choiceType of T for T].
Canonical CompleteDioid_to_Choice.
Coercion CompleteDioid_to_POrder (T : CompleteDioid.type) :=
  Eval hnf in [porderType of T for T].
Canonical CompleteDioid_to_POrder.
Coercion CompleteDioid_to_Lattice (T : CompleteDioid.type) :=
  Eval hnf in [latticeType of T for T].
Canonical CompleteDioid_to_Lattice.

Section CompleteDioidTheory.

Variables D : CompleteDioid.type.

Implicit Types a b c : D.
Implicit Types B : set D.

Definition set_add : set D -> D := set_join.

Lemma bottom_zero : bottom D = 0.
Proof. by apply/le_anti; rewrite bottom_minimum /= le0d. Qed.

Lemma set_addDl a B : set_add (a |` B) = a + set_add B.
Proof.
apply/le_anti/andP; split.
- apply: set_join_le_ub; rewrite -ubP => x [-> | Hx]; [exact: led_addr|].
  refine (le_trans _ (led_addl _ _)); exact: set_join_ub.
- rewrite led_add_eqv set_joinU_ge_r andbC /=.
  by rewrite -[in X in X <= _](set_join_set1 a) set_joinU_ge_l.
Qed.

Lemma add_def a b : a + b = a `|` b.
Proof.
rewrite -[in LHS](set_join_set1 b) -set_addDl.
by rewrite /set_add set_joinU !set_join_set1.
Qed.

Lemma set_addU A B : set_add (A `|` B) = set_add A + set_add B.
Proof. by rewrite /set_add set_joinU add_def. Qed.

Lemma add_dtop : right_zero (top D) add.
Proof. by move=> x; rewrite -set_addDl setUT. Qed.

Lemma add_topd : left_zero (top D) add.
Proof. by move=> x; rewrite adddC add_dtop. Qed.

Lemma set_add_O (F : nat -> D) : set_add [set F i | i in 'I_1] = F O.
Proof.
rewrite -(addd0 (F O)) -bottom_zero -set_addDl setU0; apply: f_equal.
by rewrite predeqP => x; split=> [[y] | ->]; [rewrite ord1|exists ord0].
Qed.

Lemma set_add_S (F : nat -> D) k :
  set_add [set F i | i in 'I_k.+1] = set_add [set F i | i in 'I_k] + F k.
Proof.
rewrite adddC -set_addDl; apply: f_equal; rewrite predeqP => x; split.
- move=> -[i Hi] <-.
  move: (leq_ord i); rewrite leq_eqVlt => /orP[/eqP -> | {}Hi]; [by left|].
  by right; exists (Ordinal Hi).
- move=> [-> | [i _ <-]]; [by exists ord_max|].
  by exists (inord i); rewrite ?inordK // ltnS ltnW.
Qed.

Lemma set_add_led (F : nat -> D) k :
  set_add [set F i | i in 'I_k] <= set_add [set of F].
Proof.
elim: k => [|k IHk].
- set S := mkset _.
  have ->: S = set0 by rewrite -subset0 => x [[]].
  exact: bottom_minimum.
- rewrite set_add_S led_add_eqv IHk /=.
  by apply: set_join_ub; exists k.
Qed.

Lemma set_add_lim_nat (F : nat -> D) l :
  (forall k, set_add [set F i | i in 'I_k] <= l) -> set_add [set of F] <= l.
Proof.
move=> H; apply: set_join_le_ub => _ [i _ <-].
by move: (H i.+1); apply/le_trans/set_join_ub; exists ord_max.
Qed.

Lemma set_add_led_set (F F' : nat -> D) :
  (forall k, set_add [set F i | i in 'I_k] <= set_add [set F' i | i in 'I_k]) ->
  set_add [set of F] <= set_add [set of F'].
Proof.
move=> H; apply: set_add_lim_nat => k.
exact/(le_trans (H k))/set_add_led.
Qed.

End CompleteDioidTheory.
