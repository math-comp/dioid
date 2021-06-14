From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import fintype ssrnat bigop.
Require Import mathcomp.analysis.classical_sets.
Require Import HB_wrappers dioid complete_lattice.

(******************************************************************************)
(* The algebraic structure of complete dioids, as described in:               *)
(*   Michel Minoux, Michel Gondran.                                           *)
(*   'Graphs, Dioids and Semirings. New Models and Algorithms.'               *)
(*   Springer, 2008                                                           *)
(*                                                                            *)
(* This file defines for each structure its type, its packers and its         *)
(* canonical properties:                                                      *)
(*                                                                            *)
(*   * CompleteDioid (dioid with infinte distributivity):                     *)
(*                   (From GONDRAN-MINOUX définition 6.1.8)                   *)
(*    CompleteDioid.yype == interface type for complete Dioid structure       *)
(* CompleteDioid_of_Dioid_and_CompleteLattice.Build D mulDl mulDr             *)
(*                       == packs a CompleteDioid; the carrier type D must    *)
(*                          have both a Dioid and a CompleteLattice canonical *)
(*                          structure (see complete_lattice.v).               *)
(*                   a^i == the power i of a                                  *)
(*                   a^* == the kleene star operator                          *)
(*                          (infinite sum of a^i, i >= 0)                     *)
(*                   a^+ == the 'plus' operator (infinite sum of a^i, i > 0)  *)
(*                 a / b == the residuation operator:                         *)
(*                          x * b <= a <-> x <= a / b                         *)
(* [CompleteDioid of U by <:] == CompleteDioid mixin for a subType whose base *)
(*                          type is both a Dioid and a CompleteLattice.       *)
(*                                                                            *)
(*   * ComCompleteDioid:                                                      *)
(* ComCompleteDioid.type == interface type for complete commutative dioid     *)
(*                          structure                                         *)
(* ComCompleteDioid_of_CompleteDioid.Build D mulC                             *)
(*                       == packs mulC into a ComCompleteDioid; the carrier   *)
(*                          type D must have a CompleteDioid canonical        *)
(*                          structure.                                        *)
(* ComCompleteDioid_of_ComDioid_and_CompleteLattice.Build D mulDl             *)
(*                       == packs mulDl into a ComCompleteDioid; the carrier  *)
(*                          type D must have both a ComDioid and a            *)
(*                          CompleteLattice canonical structure.              *)
(* ComCompleteDioid_of_CompleteLattice.Build D addA addC add0l mulA mulC      *)
(*   mul1l mulDl mul0l le_def set_mulDl                                       *)
(*                       == build a ComCompleteDioid structure from the       *)
(*                          algebraic properties of its operations.           *)
(*                          The carrier type T must have a CompleteLattice    *)
(*                          canonical structure (see complete_lattice.v).     *)
(*                                                                            *)
(* Interesting lemmas:                                                        *)
(* * forall a and b in a complete dioid, a^* * b is the least solution of     *)
(*   x = a * x + b                                                            *)
(* * forall a and b in a complete commutative dioid, (a + b)^* = a^* * b ^*   *)
(*                                                                            *)
(*   Notations are defined in scope dioid_scope (delimiter %D).               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "x ^+" (at level 2, format "x ^+").
Reserved Notation "x ^*" (at level 2, format "x ^*").

Local Open Scope classical_set_scope.
Local Open Scope order_scope.
Local Open Scope dioid_scope.

Import Order.Theory.

HB.mixin Record CompleteDioid_of_Dioid_and_CompleteLattice D
         of Dioid D & CompleteLattice D := {
  set_mulDl : forall (a : D) (B : set D),
      a * set_join B = set_join [set a * x | x in B];
  set_mulDr : forall (a : D) (B : set D),
      set_join B * a = set_join [set x * a | x in B];
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

Lemma set_add_0 (F : nat -> D) : set_add [set F i | i in [set x | 'I_0 x]] = 0.
Proof. by rewrite -bottom_zero; apply: f_equal; rewrite -subset0 => x [[]]. Qed.

Lemma set_add_1 (F : nat -> D) : set_add [set F i | i in [set x | 'I_1 x]] = F O.
Proof.
rewrite -(addd0 (F O)) -bottom_zero -set_addDl setU0; apply: f_equal.
by rewrite predeqP => x; split=> [[y] | ->]; [rewrite ord1|exists ord0].
Qed.

Lemma set_add_S (F : nat -> D) k :
  set_add [set F i | i in [set x | 'I_k.+1 x]]
  = set_add [set F i | i in [set x | 'I_k x]] + F k.
Proof.
rewrite adddC -set_addDl; apply: f_equal; rewrite predeqP => x; split.
- move=> -[i Hi] <-.
  move: (leq_ord i); rewrite leq_eqVlt => /orP[/eqP -> | {}Hi]; [by left|].
  by right; exists (Ordinal Hi).
- move=> [-> | [i _ <-]]; [by exists ord_max|].
  by exists (inord i); rewrite ?inordK // ltnS ltnW.
Qed.

Lemma set_add_led (F : nat -> D) k :
  set_add [set F i | i in [set x | 'I_k x]] <= set_add [set of F].
Proof.
elim: k => [|k IHk].
- set S := image _ _.
  have ->: S = set0 by rewrite -subset0 => x [[]].
  exact: bottom_minimum.
- rewrite set_add_S led_add_eqv IHk /=.
  by apply: set_join_ub; exists k.
Qed.

Lemma set_add_lim_nat (F : nat -> D) l :
  (forall k, set_add [set F i | i in [set x | 'I_k x]] <= l) ->
  set_add [set of F] <= l.
Proof.
move=> H; apply: set_join_le_ub => _ [i _ <-].
by move: (H i.+1); apply/le_trans/set_join_ub; exists ord_max.
Qed.

Lemma set_add_led_set (F F' : nat -> D) :
  (forall k, set_add [set F i | i in [set x | 'I_k x]]
             <= set_add [set F' i | i in [set x | 'I_k x]]) ->
  set_add [set of F] <= set_add [set of F'].
Proof.
move=> H; apply: set_add_lim_nat => k.
exact/(le_trans (H k))/set_add_led.
Qed.

Section KleeneOperatorsDefinitions.

Definition exp a n := iterop n *%D a 1.
Definition op_kleene a := set_add [set of exp a].
Definition op_plus a := set_add [set of fun i => exp a i.+1].
Definition div a b := set_add [set c | c * b <= a].

End KleeneOperatorsDefinitions.

Local Notation "a ^ i" := (exp a i) : dioid_scope.
Local Notation "a ^*" := (op_kleene a) : dioid_scope.
Local Notation "a ^+" := (op_plus a) : dioid_scope.
Local Notation "a / b" := (div a b) : dioid_scope.

Section KleeneStar.

Lemma exp0 a : a ^ 0 = 1.
Proof. by []. Qed.

Lemma expS i a : a ^ (i.+1) = a * (a ^ i).
Proof. by case: i => //; rewrite exp0 muld1. Qed.

Lemma expSr i a : a ^ i.+1 = a ^ i * a.
Proof.
elim: i => [ | i Hi]; first by rewrite exp0 mul1d.
by rewrite expS {1}Hi expS muldA.
Qed.

Lemma kleeneSr a : a^* = 1 + a^+.
Proof.
rewrite -(exp0 a) -set_addDl /op_kleene.
apply: f_equal; rewrite predeqP => b; split.
- by move=> [[| i] _ <-]; [left|right; exists i].
- by move=> [-> | [i _ <-]]; [exists O|exists i.+1].
Qed.

Lemma plusSr a : a ^+ = a * a ^*.
Proof.
rewrite set_mulDl /op_plus /op_kleene.
apply: f_equal; rewrite predeqP => b; split.
- by move=> [i _ <-]; rewrite expS; exists (a ^ i); [exists i|].
- by move=> [c [i _ <-] <-]; rewrite -expS; exists i.
Qed.

Lemma plus_le_kleene a : a^+ <= a^*.
Proof. by rewrite le_def kleeneSr adddCA adddd. Qed.

Lemma le_plus a : a <= a ^+.
Proof. by rewrite le_def plusSr kleeneSr muldDr muld1 adddA adddd. Qed.

Lemma le_kleene a : a <= a^*.
Proof. exact/(le_trans (le_plus a))/plus_le_kleene. Qed.

Lemma kleene_mul_expl a n : a ^ n * a ^* <= a^*.
Proof.
elim: n => [|n IHn]; [by rewrite mul1d|].
rewrite expSr -muldA.
move: IHn; apply/le_trans/led_mul2l.
rewrite -plusSr; apply: plus_le_kleene.
Qed.

Lemma kleene_monotony a b : a <= b -> a ^* <= b ^*.
Proof.
move=> Hab.
apply: set_add_led_set => k.
have Hyp : forall i, a ^ i <= b ^ i.
  elim=> [|i IHi].
  - by rewrite exp0.
  - by rewrite !expS; apply: led_mul.
elim: k => [|k IHk].
- by rewrite set_add_0 le0d.
- rewrite !set_add_S; exact: led_add.
Qed.

Lemma kleene_1r a : (a + 1) ^* = a ^*.
Proof.
apply/le_anti/andP; split; [|exact/kleene_monotony/led_addr].
suff Hyp : forall i, (a + 1) ^ i = set_add [set a ^ j | j in [set x | 'I_i.+1 x]].
{ apply: set_add_led_set => k.
  elim: k => [ | k IHk]; [by rewrite set_add_0 le0d|].
  rewrite !set_add_S Hyp.
  rewrite -[in X in _ <= X](adddd (set_add _)) -adddA.
  apply: (led_add IHk).
  by rewrite set_add_S. }
elim=> [ | i IHi]; [by rewrite set_add_1 !exp0|].
rewrite expS muldDl mul1d IHi set_mulDl.
set B' := [set a ^ j | j in [set j | (1 <= j <= i)%nat]].
rewrite [X in set_join X](_ : _ = a ^ i.+1 |` B'); last first.
{ rewrite predeqP => x; split.
  - move=> -[y [[j Hj] _ <-] <-].
    rewrite expS /= -!expS.
    move: Hj; rewrite leq_eqVlt ltnS => /orP[/eqP [->] | Hj]; [by left|].
    by right; exists j.+1.
  - move=> [->|]; [by rewrite expS; exists (a ^ i) => //; exists ord_max|].
    move=> -[[//|j] /andP [Hj Hji] <-]; rewrite expS; exists (a ^ j) => //.
    by move: Hji => /ltnW; rewrite -ltnS => Hji; exists (Ordinal Hji). }
rewrite -[set_join]/set_add set_addDl.
rewrite (_ : image _ _ = (1 |` B')); last first.
{ rewrite predeqP => x; split.
  { move=> -[[[|j] Hj] _ <-]; [by left; rewrite exp0|].
    by right; exists (Ordinal Hj). }
  move=> [-> | [j /= Hj <-]]; [by rewrite -(exp0 a); exists ord0|].
  by move: Hj => /andP[_]; rewrite -ltnS => Hj; exists (Ordinal Hj). }
rewrite set_addDl.
rewrite (adddC (a ^ 0)) adddA -(adddA (a ^ i.+1)) adddd adddC -!set_addDl.
apply: f_equal; rewrite predeqP => x; split.
- move=> [-> | [-> | [j /= Hj <-]]].
  + by exists ord0.
  + by exists ord_max.
  + move: Hj => /andP[_]; rewrite -ltnS; move=> /ltnW; rewrite -ltnS => Hj.
    by exists (Ordinal Hj).
- move=> -[[[|j] Hj] _ <-]; [by left|right].
  move: Hj; rewrite /nat_of_ord !ltnS leq_eqVlt => /orP[/eqP -> | ]; [by left|].
  by rewrite -ltnS => Hj; right; exists (Ordinal Hj).
Qed.

Lemma kleene_sqr a : a^* * a^* = a^*.
Proof.
rewrite {1}/op_kleene set_mulDr.
set B' := (a ^* |` [set of fun i => a ^ i.+1 * a ^*]).
rewrite (_ : image _ _ = B'); last first.
{ rewrite predeqP => x; split.
  - by move=> -[_ [[|i] _ <-] <-]; [left; rewrite exp0 mul1d|right; exists i].
  - move=> [-> | [i _ <-]]; [by exists 1; [exists O|rewrite mul1d]|].
    by exists (a ^ i.+1); [exists i.+1|]. }
rewrite -[set_join]/set_add set_addDl.
apply/eqP; rewrite adddC -le_def; apply: set_add_lim_nat.
elim=> [|k].
- by rewrite (set_add_0 (fun i => a ^ i.+1 * _)) le0d.
- rewrite (set_add_S (fun i => a ^ i.+1 * _)).
  rewrite !le_def => /eqP IHk.
  rewrite adddAC IHk adddC -le_def.
  exact: kleene_mul_expl.
Qed.

Lemma kleene_exp a i : (1 <= i)%nat -> (a ^*) ^ i = a ^*.
Proof.
case: i => [// | ] i _; elim: i => [// | i IHi].
by rewrite expS IHi kleene_sqr.
Qed.

Lemma kleene_kleene a : (a ^*) ^* = a ^*.
Proof.
rewrite kleeneSr /op_plus.
rewrite (_ : image _ _ = a ^* |` set0).
  by rewrite setU0 /set_add set_join_set1 kleeneSr adddA adddd.
rewrite predeqP => x; split.
- move=> [i _ <-]; left; exact: kleene_exp.
- by move=> [-> | //]; exists O.
Qed.

Theorem kleene_star_eq a b : a ^* * b = a * (a ^* * b) + b.
Proof. by rewrite muldA -plusSr -{3}(mul1d b) -muldDl kleeneSr adddC. Qed.

Theorem kleene_star_least a b : forall x, (x = a * x + b) -> a ^* * b <= x.
Proof.
move=> x Hx.
rewrite set_mulDr.
rewrite [X in set_join X](_ : _ = [set (a ^ i) * b | i in setT]); last first.
  rewrite predeqP => y; split.
  - by move=> [_ [i _ <-] <-]; exists i.
  - by move=> [i _ <-]; exists (a ^ i); [exists i|].
apply: set_add_lim_nat; elim=> [ | k IHk].
  by rewrite le_def (set_add_0 (fun i => a ^ i * b)) add0d.
rewrite (set_add_S (fun i => a ^ i * b)) led_add_eqv IHk /=.
elim: k {IHk} => [ | k IHk]; [by rewrite mul1d Hx led_addl|].
rewrite expS.
have Ha : a * x <= x; [by rewrite {2}Hx led_addr|].
by apply: (le_trans _ Ha); rewrite -muldA led_mul2l.
Qed.

End KleeneStar.

Section ResiduationTheory.

Lemma div_mul_le a b : (a / b) * b <= a.
Proof. by rewrite set_mulDr; apply: set_join_le_ub => y [z + <-]. Qed.

Lemma mul_div_le a b : a <= (a * b) / b.
Proof. exact/set_join_ub/lexx. Qed.

Lemma mul_div_equiv a b x : (x * a <= b) = (x <= b / a).
Proof.
apply/idP/idP.
- move=> H; exact: set_join_ub.
- move=> H.
  move: (div_mul_le b a); apply: le_trans.
  exact: led_mul2r.
Qed.

Lemma div_top x : top D / x = top D.
Proof.
apply/le_anti /andP; split; [|rewrite -mul_div_equiv]; exact: top_maximum.
Qed.

Lemma led_divl a b c : a <= b -> a / c <= b / c.
Proof. rewrite -mul_div_equiv; exact/le_trans/div_mul_le. Qed.

Lemma led_divr a b c : a <= b -> c / b <= c / a.
Proof.
move=> Hab; rewrite -mul_div_equiv.
exact/(le_trans (led_mul2l  _ Hab))/div_mul_le.
Qed.

Lemma led_div a b c d : a <= b -> d <= c -> a / c <= b / d.
Proof.
move=> Hab Hcd; rewrite -mul_div_equiv.
apply/(le_trans _ Hab); rewrite mul_div_equiv.
exact: led_divr.
Qed.

Lemma addd_div_le (a b c : D) : a / c + b / c <= (a + b) / c.
Proof.
rewrite led_add_eqv.
apply/andP; split; apply: led_divl; [exact: led_addr|exact: led_addl].
Qed.

Lemma div_mul a b c : a / (b * c) = a / c / b.
Proof.
apply/le_anti/andP; split.
- by rewrite -!mul_div_equiv -muldA; apply: div_mul_le.
- by rewrite -mul_div_equiv muldA !mul_div_equiv; exact: lexx.
Qed.

Lemma mul_divA a b c : a * (b / c) <= (a * b) / c.
Proof. rewrite -mul_div_equiv -muldA; exact/led_mul2l/div_mul_le. Qed.

Lemma kleene_div_equiv a : (a == a ^*) = (a == a / a).
Proof.
apply/idP/idP => /eqP.
- move=> ->.
  apply/eqP/le_anti/andP; split.
  + apply: set_join_le_ub => _ [i _ <-].
    rewrite -mul_div_equiv.
    exact: kleene_mul_expl.
  + apply: set_join_le_ub => x /=.
    rewrite {1}kleeneSr muldDr muld1.
    by rewrite led_add_eqv => /andP[].
- move=> Ha; apply/eqP/le_anti/andP; split; [exact: le_kleene|].
  apply: set_join_le_ub => _ [i _ <-].
  elim: i => [ | i IHi]; [by rewrite exp0 Ha -mul_div_equiv mul1d|].
  by rewrite expSr mul_div_equiv -Ha.
Qed.

Lemma mul_kleene a b : a * b ^* = (a * b ^*) / b ^*.
Proof.
apply/le_anti/andP; split.
- by rewrite -mul_div_equiv -muldA kleene_sqr.
- apply: set_join_le_ub => x.
  apply: le_trans.
  by rewrite kleeneSr muldDr muld1 led_addr.
Qed.

Lemma div_kleene a b : a / b ^* = (a / b ^*) * b ^*.
Proof.
apply/le_anti/andP; split; last first.
- by rewrite -mul_div_equiv -muldA kleene_sqr div_mul_le.
- apply: set_join_le_ub => x /=.
  rewrite mul_div_equiv => Hx.
  apply: (le_trans Hx).
  by rewrite kleeneSr muldDr muld1 led_addr.
Qed.

End ResiduationTheory.

End CompleteDioidTheory.

HB.structure Definition ComCompleteDioid :=
  { D of ComSemiRing D & CompleteDioid D }.

HB.factory Record ComCompleteDioid_of_ComDioid_and_CompleteLattice D
           of ComDioid D & CompleteLattice D := {
  set_mulDl : forall (a : D) (B : set D),
      a * set_join B = set_join [set a * x | x in B];
}.

HB.builders Context D (f : ComCompleteDioid_of_ComDioid_and_CompleteLattice D).

  Lemma set_mulDr a (B : set D) :
    set_join B * a = set_join [set x * a | x in B].
  Proof.
  by rewrite muldC set_mulDl; apply: f_equal; rewrite predeqP => x; split;
    (move=> -[y Hy <-]; exists y; [|rewrite muldC]).
  Qed.

  HB.instance Definition to_CompleteDioid_of_Dioid_and_CompleteLattice :=
    CompleteDioid_of_Dioid_and_CompleteLattice.Build D set_mulDl set_mulDr.

HB.end.

HB.factory Record ComCompleteDioid_of_CompleteLattice D
           of CompleteLattice D := {
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
  set_mulDl : forall (a : D) (B : set D),
      mul a (set_join B) = set_join [set mul a x | x in B];
}.

HB.builders Context D (f : ComCompleteDioid_of_CompleteLattice D).

  HB.instance Definition to_ComDioid_of_WrapPOrder :=
    ComDioid_of_WrapPOrder.Build
      D adddA adddC add0d adddd
      muldA muldC mul1d muldDl mul0d le_def.

  HB.instance Definition to_ComCompleteDioid_of_ComDioid_and_CompleteLattice :=
    ComCompleteDioid_of_ComDioid_and_CompleteLattice.Build
      D set_mulDl.

HB.end.

Section ComCompleteDioidTheory.

Variables D : ComCompleteDioid.type.

Implicit Types a b : D.

Local Notation "a ^ i" := (@exp _ a i) : dioid_scope.
Local Notation "a ^*" := (@op_kleene _ a) : dioid_scope.
Local Notation "a ^+" := (@op_plus _ a) : dioid_scope.
Local Notation "a / b" := (div a b) : dioid_scope.

Section ComResiduationTheory.

Lemma divAC : right_commutative (@div D).
Proof.
move=> a b c; apply/le_anti/andP; split; rewrite -!mul_div_equiv.
- by rewrite -muldA (muldC b) muldA !mul_div_equiv.
- by rewrite -muldA (muldC c) muldA !mul_div_equiv.
Qed.

Lemma kleene_add_mul a b : (a + b) ^* = a ^* * b ^*.
Proof.
apply/le_anti/andP; split.
- apply: set_join_le_ub => _ [i _ <-].
  elim: i => [ | i IHi].
  + rewrite exp0 -(muld1 1).
    apply: led_mul.
    * rewrite kleeneSr -{1}(addd0 1).
      exact/led_add2l/le0d.
    * rewrite kleeneSr -{1}(addd0 1).
      exact/led_add2l/le0d.
  + rewrite expS.
    apply: (le_trans (led_mul2l _ IHi)).
    rewrite muldDl muldA -plusSr (muldC b) -muldA -(muldC b) -plusSr.
    rewrite !kleeneSr !muldDl !muldDr !muld1 !mul1d.
    rewrite !adddA (adddC (a^+)) adddC !adddA adddd.
    rewrite [X in _ <= X]adddC -!adddA (adddC 1) (adddC (a^+)) !adddA.
    exact: led_addr.
- rewrite {2}/op_kleene /set_add set_mulDl.
  apply: set_join_le_ub => _ [_ [i _ <-] <-].
  rewrite {1}/op_kleene /set_add set_mulDr.
  apply: set_join_le_ub => _ [_ [j _ <-] <-].
  elim: i => [ | i HIi].
  + rewrite exp0 muld1.
    elim: j => [ | j HIj]; [by rewrite exp0 kleeneSr led_addr|].
    rewrite expS kleeneSr plusSr -(add0d (_ * _)).
    apply: led_add; [exact: le0d|].
    apply: led_mul => [ | //].
    exact: led_addr.
  + rewrite expS (muldC b) muldA.
    apply: (le_trans (led_mul2r _ HIi)).
    rewrite muldC {2}kleeneSr plusSr -(add0d (_ * _)).
    apply: led_add; [exact: le0d|].
    exact/led_mul2r/led_addl.
Qed.

End ComResiduationTheory.

End ComCompleteDioidTheory.

Module SubType.

Section CompleteDioid.

Variables (V : CompleteDioid.type) (S : pred V).
Variable (U : subType S).

Variable D : Dioid.type.
Variable cD : Dioid.axioms U.
Hypothesis uUD : unify Type Type U D None.
Hypothesis uUD' :
  unify Dioid.type Dioid.type D (Dioid.Pack cD) None.
Let U' := @Dioid.phant_clone U D cD uUD uUD'.

Variable L : CompleteLattice.type.
Variable cL : CompleteLattice.axioms U'.
Hypothesis uU'L : unify Type Type U' L None.
Hypothesis uU'L' :
  unify CompleteLattice.type CompleteLattice.type L (CompleteLattice.Pack cL) None.
Let U'' := @CompleteLattice.phant_clone U' L cL uU'L uU'L'.

Hypothesis valM : forall x y : U'', val (x * y) = val x * val y.
Hypothesis valSJ : forall B : set U'', val (set_join B) = set_join (val @` B).

Lemma set_mulDl (a : U'') (B : set U'') :
  a * set_join B = set_join [set (a * x : U'') | x in B].
Proof.
apply/val_inj; rewrite valM !valSJ set_mulDl.
apply: f_equal; rewrite predeqP => x; split.
- move=> -[_ [y Hy <-] <-].
  by exists (a * y) => //; exists y.
- move=> -[_ [y Hy <-] <-].
  by exists (val y) => //; exists y.
Qed.

Lemma set_mulDr (a : U'') (B : set U'') :
  set_join B * a = set_join [set (x * a : U'') | x in B].
Proof.
apply/val_inj; rewrite valM !valSJ set_mulDr.
apply: f_equal; rewrite predeqP => x; split.
- move=> -[_ [y Hy <-] <-].
  by exists ((y : U'') * a) => //; exists y.
- move=> -[_ [y Hy <-] <-].
  by exists (val y) => //; exists y.
Qed.

End CompleteDioid.

Module Exports.

Notation "[ 'CompleteDioid' 'of' R 'by' <: ]" :=
  (CompleteDioid_of_Dioid_and_CompleteLattice.Build
     R
     (@SubType.set_mulDl
        _ _ _ (Dioid.clone R _) _ id_phant id_phant
        (CompleteLattice.clone R _) _ id_phant id_phant (rrefl _) (frefl _))
     (@SubType.set_mulDr
        _ _ _ (Dioid.clone R _) _ id_phant id_phant
        (CompleteLattice.clone R _) _ id_phant id_phant (rrefl _) (frefl _)))
  (at level 0, format "[ 'CompleteDioid' 'of' R 'by' <: ]") : form_scope.

End Exports.

End SubType.

Export SubType.Exports.

Notation "a ^ i" := (@exp _ a i) : dioid_scope.
Notation "a ^*" := (@op_kleene _ a) : dioid_scope.
Notation "a ^+" := (@op_plus _ a) : dioid_scope.
Notation "a / b" := (div a b) : dioid_scope.
