From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import fintype ssrnat bigop ssralg boolp classical_sets.
Require Import dioid complete_lattice.

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
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope dioid_scope.

Import Order.Theory GRing.Theory.

HB.mixin Record isCompleteDioid d D of Dioid d D & CompleteLattice d D := {
  set_mulDl : forall (a : D) (B : set D),
      a * set_join B = set_join [set a * x | x in B];
  set_mulDr : forall (a : D) (B : set D),
      set_join B * a = set_join [set x * a | x in B];
}.

#[short(type="dioidCompleteLatticeType")]
HB.structure Definition DioidCompleteLattice d :=
  { D of Dioid d D & CompleteLattice d D }.

#[short(type="completeDioidType")]
HB.structure Definition CompleteDioid d :=
  { D of DioidCompleteLattice d D & isCompleteDioid d D }.

Section CompleteDioidTheory.

Variables (disp : unit) (D : completeDioidType disp).

Implicit Types a b c : D.
Implicit Types B : set D.

Notation set_add := set_join.

Lemma bottom_zero : 0%O = 0%R :> D.
Proof. by apply/le_anti; rewrite le0x le0d. Qed.

Lemma set_addDl a B : set_add (a |` B) = a + set_add B.
Proof.
apply/le_anti/andP; split.
- apply: set_join_le_ub => x [-> | Bx]; [exact: led_addr|].
  by apply: le_trans (led_addl _ _); apply: set_join_ub.
- by rewrite led_addE set_joinU_ge_r andbT -[leLHS](set_join1 a) set_joinU_ge_l.
Qed.

Lemma add_join a b : a + b = a `|` b.
Proof. by rewrite -[in LHS](set_join1 b) -set_addDl set_joinU !set_join1. Qed.

Lemma set_addU A B : set_add (A `|` B) = set_add A + set_add B.
Proof. by rewrite set_joinU add_join. Qed.

Lemma add_d1 : @right_zero D D 1%O +%R.
Proof. by move=> x; apply/eqP; rewrite -le_def lex1. Qed.

Lemma add_1d : @left_zero D D 1%O +%R.
Proof. by move=> x; rewrite addrC add_d1. Qed.

Lemma set_add0 (F : nat -> D) : set_add [set F i | i in [set x | 'I_0 x]] = 0%R.
Proof.
by rewrite -bottom_zero -set_join0; congr set_add; rewrite -subset0 => x [[]].
Qed.

Lemma set_add1 (F : nat -> D) : set_add [set F i | i in [set x | 'I_1 x]] = F O.
Proof.
rewrite -(addr0 (F O)) -bottom_zero -set_join0 -set_addDl setU0; congr set_add.
by rewrite predeqP => x; split=> [[y] | ->]; [rewrite ord1|exists ord0].
Qed.

Lemma set_addS (F : nat -> D) k :
  set_add [set F i | i in [set x | 'I_k.+1 x]]
  = set_add [set F i | i in [set x | 'I_k x]] + F k.
Proof.
rewrite addrC -set_addDl; congr set_add; rewrite predeqP => x; split.
- move=> -[i Hi] <-.
  move: (leq_ord i); rewrite leq_eqVlt => /orP[/eqP -> | {}Hi]; [by left|].
  by right; exists (Ordinal Hi).
- move=> [-> | [i _ <-]]; [by exists ord_max|].
  by exists (inord i); rewrite ?inordK // ltnS ltnW.
Qed.

Lemma set_add_led (F : nat -> D) k :
  set_add [set F i | i in [set x | 'I_k x]] <= set_add (range F).
Proof.
elim: k => [|k IHk].
- set S := image _ _.
  have ->: S = set0 by rewrite -subset0 => x [[]].
  by rewrite set_join0 le0x.
- rewrite set_addS led_addE IHk /=.
  by apply: set_join_ub; exists k.
Qed.

Lemma set_add_lim_nat (F : nat -> D) l :
  (forall k, set_add [set F i | i in [set x | 'I_k x]] <= l) ->
  set_add (range F) <= l.
Proof.
move=> H; apply: set_join_le_ub => _ [i _ <-].
by move: (H i.+1); apply/le_trans/set_join_ub; exists ord_max.
Qed.

Lemma set_add_led_set (F F' : nat -> D) :
  (forall k, set_add [set F i | i in [set x | 'I_k x]]
             <= set_add [set F' i | i in [set x | 'I_k x]]) ->
  set_add (range F) <= set_add (range F').
Proof.
move=> H; apply: set_add_lim_nat => k.
exact/(le_trans (H k))/set_add_led.
Qed.

Section KleeneOperatorsDefinitions.

Definition exp a n := iterop n *%R a 1%R.
Definition op_kleene a := set_add (range (exp a)).
Definition op_plus a := set_add (range (fun i => exp a i.+1)).
Definition div a b := set_add [set c | c * b <= a].

End KleeneOperatorsDefinitions.

Local Notation "a ^ i" := (exp a i) : dioid_scope.
Local Notation "a ^*" := (op_kleene a) : dioid_scope.
Local Notation "a ^+" := (op_plus a) : dioid_scope.
Local Notation "a / b" := (div a b) : dioid_scope.

Section KleeneStar.

Lemma exp0 a : a ^ 0 = 1%R.
Proof. by []. Qed.

Lemma expS i a : a ^ (i.+1) = a * (a ^ i).
Proof. by case: i => //; rewrite exp0 mulr1. Qed.

Lemma expSr i a : a ^ i.+1 = a ^ i * a.
Proof.
elim: i => [ | i Hi]; first by rewrite exp0 mul1r.
by rewrite expS {1}Hi expS mulrA.
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
Proof. by rewrite le_def kleeneSr addrCA adddd. Qed.

Lemma le_plus a : a <= a ^+.
Proof. by rewrite le_def plusSr kleeneSr mulrDr mulr1 addrA adddd. Qed.

Lemma le_kleene a : a <= a^*.
Proof. exact/(le_trans (le_plus a))/plus_le_kleene. Qed.

Lemma kleene_mul_expl a n : a ^ n * a ^* <= a^*.
Proof.
elim: n => [|n IHn]; [by rewrite mul1r|].
rewrite expSr -mulrA.
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
- by rewrite set_add0 le0d.
- rewrite !set_addS; exact: led_add.
Qed.

Lemma kleene_1r a : (a + 1) ^* = a ^*.
Proof.
apply/le_anti/andP; split; [|exact/kleene_monotony/led_addr].
suff Hyp : forall i, (a + 1) ^ i = set_add [set a ^ j | j in [set x | 'I_i.+1 x]].
{ apply: set_add_led_set => k.
  elim: k => [ | k IHk]; [by rewrite set_add0 le0d|].
  rewrite !set_addS Hyp.
  rewrite -[in X in _ <= X](adddd (set_add _)) -addrA.
  apply: (led_add IHk).
  by rewrite set_addS. }
elim=> [ | i IHi]; [by rewrite set_add1 !exp0|].
rewrite expS mulrDl mul1r IHi set_mulDl.
set B' := [set a ^ j | j in [set j | (1 <= j <= i)%N]].
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
rewrite (_ : image _ _ = (1%R |` B')); last first.
{ rewrite predeqP => x; split.
  { move=> -[[[|j] Hj] _ <-]; [by left; rewrite exp0|].
    by right; exists (Ordinal Hj). }
  move=> [-> | [j /= Hj <-]]; [by rewrite -(exp0 a); exists ord0|].
  by move: Hj => /andP[_]; rewrite -ltnS => Hj; exists (Ordinal Hj). }
rewrite set_addDl.
rewrite (addrC (a ^ 0)) addrA -(addrA (a ^ i.+1)) adddd addrC -!set_addDl.
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
set B' := (a ^* |` (range (fun i => a ^ i.+1 * a ^*))).
rewrite (_ : image _ _ = B'); last first.
{ rewrite predeqP => x; split.
  - by move=> -[_ [[|i] _ <-] <-]; [left; rewrite exp0 mul1r|right; exists i].
  - move=> [-> | [i _ <-]]; [by exists 1%R; [exists O|rewrite mul1r]|].
    by exists (a ^ i.+1); [exists i.+1|]. }
rewrite -[set_join]/set_add set_addDl.
apply/eqP; rewrite addrC -le_def; apply: set_add_lim_nat.
elim=> [|k].
- by rewrite (set_add0 (fun i => a ^ i.+1 * _)) le0d.
- rewrite (set_addS (fun i => a ^ i.+1 * _)).
  rewrite !le_def => /eqP IHk.
  rewrite addrAC IHk addrC -le_def.
  exact: kleene_mul_expl.
Qed.

Lemma kleene_exp a i : (1 <= i)%N -> (a ^*) ^ i = a ^*.
Proof.
case: i => [// | ] i _; elim: i => [// | i IHi].
by rewrite expS IHi kleene_sqr.
Qed.

Lemma kleene_kleene a : (a ^*) ^* = a ^*.
Proof.
rewrite kleeneSr /op_plus.
rewrite (_ : image _ _ = a ^* |` set0).
  by rewrite setU0 set_join1 kleeneSr addrA adddd.
rewrite predeqP => x; split.
- move=> [i _ <-]; left; exact: kleene_exp.
- by move=> [-> | //]; exists O.
Qed.

Theorem kleene_star_eq a b : a ^* * b = a * (a ^* * b) + b.
Proof. by rewrite mulrA -plusSr -{3}(mul1r b) -mulrDl kleeneSr addrC. Qed.

Theorem kleene_star_least a b : forall x, (x = a * x + b) -> a ^* * b <= x.
Proof.
move=> x Hx.
rewrite set_mulDr.
rewrite [X in set_join X](_ : _ = [set (a ^ i) * b | i in setT]); last first.
  rewrite predeqP => y; split.
  - by move=> [_ [i _ <-] <-]; exists i.
  - by move=> [i _ <-]; exists (a ^ i); [exists i|].
apply: set_add_lim_nat; elim=> [ | k IHk].
  by rewrite le_def (set_add0 (fun i => a ^ i * b)) add0r.
rewrite (set_addS (fun i => a ^ i * b)) led_addE IHk /=.
elim: k {IHk} => [ | k IHk]; [by rewrite mul1r Hx led_addl|].
rewrite expS.
have Ha : a * x <= x; [by rewrite {2}Hx led_addr|].
by apply: (le_trans _ Ha); rewrite -mulrA led_mul2l.
Qed.

End KleeneStar.

Section ResiduationTheory.

Lemma div_mul_le a b : (a / b)%D * b <= a.
Proof. by rewrite set_mulDr; apply: set_join_le_ub => y [z + <-]. Qed.

Lemma mul_div_le a b : a <= (a * b) / b.
Proof. exact/set_join_ub/lexx. Qed.

Lemma mul_div_equiv a b x : (x * a <= b) = (x <= b / a).
Proof.
apply/idP/idP => H; [exact: set_join_ub|].
by move: (div_mul_le b a); apply/le_trans/led_mul2r.
Qed.

Lemma div_top x : 1%O / x = 1%O.
Proof. apply/le_anti /andP; split; [|rewrite -mul_div_equiv]; exact: lex1. Qed.

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

Lemma addd_div_le a b c : (a / c)%D + (b / c)%D <= (a + b) / c.
Proof.
rewrite led_addE.
apply/andP; split; apply: led_divl; [exact: led_addr|exact: led_addl].
Qed.

Lemma div_mul a b c : a / (b * c) = a / c / b.
Proof.
apply/le_anti/andP; split.
- by rewrite -!mul_div_equiv -mulrA; apply: div_mul_le.
- by rewrite -mul_div_equiv mulrA !mul_div_equiv; exact: lexx.
Qed.

Lemma mul_divA a b c : a * (b / c)%D <= (a * b) / c.
Proof. rewrite -mul_div_equiv -mulrA; exact/led_mul2l/div_mul_le. Qed.

Lemma kleene_div_equiv a : (a == a ^*) = (a == a / a).
Proof.
apply/idP/idP => /eqP.
- move=> ->.
  apply/eqP/le_anti/andP; split.
  + apply: set_join_le_ub => _ [i _ <-].
    rewrite -mul_div_equiv.
    exact: kleene_mul_expl.
  + apply: set_join_le_ub => x /=.
    rewrite {1}kleeneSr mulrDr mulr1.
    by rewrite led_addE => /andP[].
- move=> Ha; apply/eqP/le_anti/andP; split; [exact: le_kleene|].
  apply: set_join_le_ub => _ [i _ <-].
  elim: i => [ | i IHi]; [by rewrite exp0 Ha -mul_div_equiv mul1r|].
  by rewrite expSr mul_div_equiv -Ha.
Qed.

Lemma mul_kleene a b : a * b ^* = (a * b ^*) / b ^*.
Proof.
apply/le_anti/andP; split.
- by rewrite -mul_div_equiv -mulrA kleene_sqr.
- apply: set_join_le_ub => x.
  apply: le_trans.
  by rewrite kleeneSr mulrDr mulr1 led_addr.
Qed.

Lemma div_kleene a b : a / b ^* = (a / b ^*)%D * b ^*.
Proof.
apply/le_anti/andP; split; last first.
- by rewrite -mul_div_equiv -mulrA kleene_sqr div_mul_le.
- apply: set_join_le_ub => x /=.
  rewrite mul_div_equiv => Hx.
  apply: (le_trans Hx).
  by rewrite kleeneSr mulrDr mulr1 led_addr.
Qed.

End ResiduationTheory.

End CompleteDioidTheory.

Notation "a ^ i" := (exp a i) : dioid_scope.
Notation "a ^*" := (op_kleene a) : dioid_scope.
Notation "a ^+" := (op_plus a) : dioid_scope.
Notation "a / b" := (div a b) : dioid_scope.

#[short(type="comCompleteDioidType")]
HB.structure Definition ComCompleteDioid d :=
  { D of GRing.ComSemiRing D & CompleteDioid d D }.

HB.factory Record isComCompleteDioid d D
    of ComDioid d D & CompleteLattice d D := {
  set_mulDl : forall (a : D) (B : set D),
    a * set_join B = set_join [set a * x | x in B];
}.

HB.builders Context d D of isComCompleteDioid d D.
Lemma set_mulDr a (B : set D) :
  set_join B * a = set_join [set x * a | x in B].
Proof.
by rewrite mulrC set_mulDl; apply: f_equal; rewrite predeqP => x; split;
  (move=> -[y Hy <-]; exists y; [|rewrite mulrC]).
Qed.
HB.instance Definition _ := isCompleteDioid.Build d D set_mulDl set_mulDr.
HB.end.

HB.factory Record CompleteLattice_isComCompleteDioid d D
    of CompleteLattice d D := {
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
  set_mulDl : forall (a : D) (B : set D),
    mul a (set_join B) = set_join [set mul a x | x in B];
}.

HB.builders Context d D of CompleteLattice_isComCompleteDioid d D.
HB.instance Definition _ := POrder_isComDioid.Build d D
  addA addC add0d adddd mulA mulC mul1d mulDl mul0d oner_neq0 le_def.
HB.instance Definition _ := isComCompleteDioid.Build d D set_mulDl.
HB.end.

Section ComCompleteDioidTheory.

Variables (disp : unit) (D : comCompleteDioidType disp).

Implicit Types a b : D.

Section ComResiduationTheory.

Lemma divAC : right_commutative (@div _ D).
Proof.
move=> a b c; apply/le_anti/andP; split; rewrite -!mul_div_equiv.
- by rewrite -mulrA (mulrC b) mulrA !mul_div_equiv.
- by rewrite -mulrA (mulrC c) mulrA !mul_div_equiv.
Qed.

Lemma kleene_add_mul a b : (a + b) ^* = a ^* * b ^*.
Proof.
apply/le_anti/andP; split.
- apply: set_join_le_ub => _ [i _ <-].
  elim: i => [ | i IHi].
  + rewrite exp0 -(mulr1 1%R).
    apply: led_mul.
    * rewrite kleeneSr -{1}(addr0 1%R).
      exact/led_add2l/le0d.
    * rewrite kleeneSr -{1}(addr0 1%R).
      exact/led_add2l/le0d.
  + rewrite expS.
    apply: (le_trans (led_mul2l _ IHi)).
    rewrite mulrDl mulrA -plusSr (mulrC b) -mulrA -(mulrC b) -plusSr.
    rewrite !kleeneSr !mulrDl !mulrDr !mulr1 !mul1r.
    rewrite !addrA (addrC (a^+)) addrC !addrA adddd.
    rewrite [X in _ <= X]addrC -!addrA (addrC 1%R) (addrC (a^+)) !addrA.
    exact: led_addr.
- rewrite {2}/op_kleene set_mulDl.
  apply: set_join_le_ub => _ [_ [i _ <-] <-].
  rewrite {1}/op_kleene set_mulDr.
  apply: set_join_le_ub => _ [_ [j _ <-] <-].
  elim: i => [ | i HIi].
  + rewrite exp0 mulr1.
    elim: j => [ | j HIj]; [by rewrite exp0 kleeneSr led_addr|].
    rewrite expS kleeneSr plusSr -(add0r (_ * _)).
    apply: led_add; [exact: le0d|].
    apply: led_mul => [ | //].
    exact: led_addr.
  + rewrite expS (mulrC b) mulrA.
    apply: (le_trans (led_mul2r _ HIi)).
    rewrite mulrC {2}kleeneSr plusSr -(add0r (_ * _)).
    apply: led_add; [exact: le0d|].
    exact/led_mul2r/led_addl.
Qed.

End ComResiduationTheory.

End ComCompleteDioidTheory.

#[short(type="subDioidCompleteLatticeType")]
HB.structure Definition SubDioidCompleteLattice d
    (D : dioidCompleteLatticeType d) S d' :=
  { U of @SubDioid d D S d' U & CompleteLattice d' U }.

#[short(type="joinSubCompleteDioidType")]
HB.structure Definition JoinSubCompleteDioid d (D : completeDioidType d) S d' :=
  { U of @SubDioid d D S d' U & @JoinSubCompleteLattice d D S d' U
    & CompleteDioid d' U }.

#[short(type="subCompleteDioidType")]
HB.structure Definition SubCompleteDioid d (D : completeDioidType d) S d' :=
  { U of @SubDioid d D S d' U & @SubCompleteLattice d D S d' U
    & CompleteDioid d' U }.

HB.factory Record SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid
    d (D : completeDioidType d) S d' U
    of @SubDioid d D S d' U & @JoinSubCompleteLattice d D S d' U := {}.

HB.builders Context d D S d' U
  of SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid d D S d' U.
Lemma set_mulDl (a : U) (B : set U) :
  a * set_join B = set_join [set a * x | x in B].
Proof.
apply/val_inj; rewrite rmorphM/= !omorphSJ/= set_mulDl !image_comp.
by congr set_join; apply/eq_imagel => x Bx; rewrite /= rmorphM.
Qed.
Lemma set_mulDr (a : U) (B : set U) :
  set_join B * a = set_join [set x * a | x in B].
Proof.
apply/val_inj; rewrite rmorphM/= !omorphSJ/= set_mulDr !image_comp.
by congr set_join; apply/eq_imagel => x Bx; rewrite /= rmorphM.
Qed.
HB.instance Definition _ := isCompleteDioid.Build d' U set_mulDl set_mulDr.
HB.end.

HB.factory Record SubDioid_SubPOrder_isJoinSubCompleteDioid d
    (D : completeDioidType d) S d' U
    of @SubDioid d D S d' U & @Order.SubPOrder d D S d' U := {
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d D S d' U
  of SubDioid_SubPOrder_isJoinSubCompleteDioid d D S d' U.
HB.instance Definition _ := SubPOrder_isJoinSubCompleteLattice.Build d D S d' U
  opredSJ_subproof.
HB.instance Definition _ :=
  SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid.Build d D S d' U.
HB.end.

HB.factory Record SubChoice_isJoinSubCompleteDioid d (D : completeDioidType d)
    S (d' : unit) U of SubChoice D S U := {
  semiring_closed_subproof : semiring_closed S;
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d D S d' U of SubChoice_isJoinSubCompleteDioid d D S d' U.
HB.instance Definition _ := SubChoice_isSubDioid.Build d D S d' U
  semiring_closed_subproof.
HB.instance Definition _ :=
  SubDioid_SubPOrder_isJoinSubCompleteDioid.Build d D S d' U opredSJ_subproof.
HB.end.

HB.factory Record SubChoice_isJoinSubComCompleteDioid
    d (D : comCompleteDioidType d) S (d' : unit) U of SubChoice D S U := {
  semiring_closed_subproof : semiring_closed S;
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d D S d' U
  of SubChoice_isJoinSubComCompleteDioid d D S d' U.
HB.instance Definition _ := SubChoice_isJoinSubCompleteDioid.Build d D S d' U
  semiring_closed_subproof opredSJ_subproof.
HB.instance Definition _ := GRing.SubSemiRing_isSubComSemiRing.Build D S U.
HB.end.

HB.factory Record SubDioid_SubCompleteLattice_isSubCompleteDioid
    d (D : completeDioidType d) S d' U
    of @SubDioid d D S d' U & @SubCompleteLattice d D S d' U := {}.

HB.builders Context d D S d' U
  of SubDioid_SubCompleteLattice_isSubCompleteDioid d D S d' U.
Lemma set_mulDl (a : U) (B : set U) :
  a * set_join B = set_join [set a * x | x in B].
Proof.
apply/val_inj; rewrite rmorphM/= !omorphSJ/= set_mulDl !image_comp.
by congr set_join; apply/eq_imagel => x Bx; rewrite /= rmorphM.
Qed.
Lemma set_mulDr (a : U) (B : set U) :
  set_join B * a = set_join [set x * a | x in B].
Proof.
apply/val_inj; rewrite rmorphM/= !omorphSJ/= set_mulDr !image_comp.
by congr set_join; apply/eq_imagel => x Bx; rewrite /= rmorphM.
Qed.
HB.instance Definition _ := isCompleteDioid.Build d' U set_mulDl set_mulDr.
HB.end.

HB.factory Record SubDioid_SubPOrder_isSubCompleteDioid d
    (D : completeDioidType d) S d' U
    of @SubDioid d D S d' U & @Order.SubPOrder d D S d' U := {
  opredSM_subproof : set_meet_closed S;
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d D S d' U
  of SubDioid_SubPOrder_isSubCompleteDioid d D S d' U.
HB.instance Definition _ := SubPOrder_isSubCompleteLattice.Build d D S d' U
  opredSM_subproof opredSJ_subproof.
HB.instance Definition _ :=
  SubDioid_SubCompleteLattice_isSubCompleteDioid.Build d D S d' U.
HB.end.

HB.factory Record SubChoice_isSubCompleteDioid d (D : completeDioidType d) S
    (d' : unit) U of SubChoice D S U := {
  semiring_closed_subproof : semiring_closed S;
  opredSM_subproof : set_meet_closed S;
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d D S d' U of SubChoice_isSubCompleteDioid d D S d' U.
HB.instance Definition _ := SubChoice_isSubDioid.Build d D S d' U
  semiring_closed_subproof.
HB.instance Definition _ :=
  SubDioid_SubPOrder_isSubCompleteDioid.Build d D S d' U
    opredSM_subproof opredSJ_subproof.
HB.end.

HB.factory Record SubChoice_isSubComCompleteDioid
    d (D : comCompleteDioidType d) S (d' : unit) U of SubChoice D S U := {
  semiring_closed_subproof : semiring_closed S;
  opredSM_subproof : set_meet_closed S;
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d D S d' U
  of SubChoice_isSubComCompleteDioid d D S d' U.
HB.instance Definition _ := SubChoice_isSubCompleteDioid.Build d D S d' U
  semiring_closed_subproof opredSM_subproof opredSJ_subproof.
HB.instance Definition _ := GRing.SubSemiRing_isSubComSemiRing.Build D S U.
HB.end.

Notation "[ 'SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid' 'of' U 'by' <: ]" :=
  (SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid.Build _ _ _ _ U)
  (at level 0, format "[ 'SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid.Build _ _ _ disp U)
  (at level 0, format "[ 'SubDioid_JoinSubCompleteLattice_isJoinSubCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubDioid_SubPOrder_isJoinSubCompleteDioid' 'of' U 'by' <: ]" :=
  (SubDioid_SubPOrder_isJoinSubCompleteDioid.Build _ _ _ _ U (opredSJ _))
  (at level 0, format "[ 'SubDioid_SubPOrder_isJoinSubCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubDioid_SubPOrder_isJoinSubCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubDioid_SubPOrder_isJoinSubCompleteDioid.Build _ _ _ disp U (opredSJ _))
  (at level 0, format "[ 'SubDioid_SubPOrder_isJoinSubCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isJoinSubCompleteDioid' 'of' U 'by' <: ]" :=
  (SubChoice_isJoinSubCompleteDioid.Build _ _ _ _ U (semiringClosedP _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isJoinSubCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isJoinSubCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isJoinSubCompleteDioid.Build _ _ _ disp U (semiringClosedP _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isJoinSubCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isJoinSubComCompleteDioid' 'of' U 'by' <: ]" :=
  (SubChoice_isJoinSubComCompleteDioid.Build _ _ _ _ U (semiringClosedP _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isJoinSubComCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isJoinSubComCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isJoinSubComCompleteDioid.Build _ _ _ disp U (semiringClosedP _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isJoinSubComCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubDioid_SubCompleteLattice_isSubCompleteDioid' 'of' U 'by' <: ]" :=
  (SubDioid_SubCompleteLattice_isSubCompleteDioid.Build _ _ _ _ U)
  (at level 0, format "[ 'SubDioid_SubCompleteLattice_isSubCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubDioid_SubCompleteLattice_isSubCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubDioid_SubCompleteLattice_isSubCompleteDioid.Build _ _ _ disp U)
  (at level 0, format "[ 'SubDioid_SubCompleteLattice_isSubCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubDioid_SubPOrder_isSubCompleteDioid' 'of' U 'by' <: ]" :=
  (SubDioid_SubPOrder_isSubCompleteDioid.Build _ _ _ _ U (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubDioid_SubPOrder_isSubCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubDioid_SubPOrder_isSubCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubDioid_SubPOrder_isSubCompleteDioid.Build _ _ _ disp U (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubDioid_SubPOrder_isSubCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubCompleteDioid' 'of' U 'by' <: ]" :=
  (SubChoice_isSubCompleteDioid.Build _ _ _ _ U (semiringClosedP _) (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isSubCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubCompleteDioid.Build _ _ _ disp U (semiringClosedP _) (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isSubCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComCompleteDioid' 'of' U 'by' <: ]" :=
  (SubChoice_isSubComCompleteDioid.Build _ _ _ _ U (semiringClosedP _) (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isSubComCompleteDioid'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubComCompleteDioid' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubComCompleteDioid.Build _ _ _ disp U (semiringClosedP _) (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isSubComCompleteDioid'  'of'  U  'by'  <:  'with'  disp ]")
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

Module Test1.
Section Test1.

Variables (d : unit) (D : completeDioidType d) (S : semiringClosed D).
Hypothesis SSJ : set_join_closed S.

HB.instance Definition _ := isJoinCompleteLatticeClosed.Build d D S SSJ.

HB.instance Definition _ :=
  [SubChoice_isJoinSubCompleteDioid of B S by <: with tt].

End Test1.
End Test1.

Module Test2.
Section Test2.

Variables (d : unit) (D : completeDioidType d) (S : semiringClosed D).
Hypothesis SSM : set_meet_closed S.
Hypothesis SSJ : set_join_closed S.

HB.instance Definition _ := isCompleteLatticeClosed.Build d D S SSM SSJ.

HB.instance Definition _ := [SubChoice_isSubCompleteDioid of B S by <: with tt].

End Test2.
End Test2.

Module Test3.
Section Test3.

Variables (d : unit) (D : comCompleteDioidType d) (S : semiringClosed D).
Hypothesis SSJ : set_join_closed S.

HB.instance Definition _ := isJoinCompleteLatticeClosed.Build d D S SSJ.

HB.instance Definition _ :=
  [SubChoice_isJoinSubComCompleteDioid of B S by <: with tt].

End Test3.
End Test3.

*)

(* end hide *)
