From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat bigop classical_sets.

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
(*     set_join_closed S <-> collective predicate S is closed under join      *)
(* SetJoinPred set_joinS == packs set_joinS : set_join_closed S into a        *)
(*                          setJoinPred S interface structure associating     *)
(*                          this property to the canonical pred_key S, i.e    *)
(*                          the k for wich S has a Canonical keyed_pred k     *)
(*                          structure. (see file ssrbool.v)                   *)
(* [CompleteLattice of U by <:] == CompleteLattice mixin for a subType whose  *)
(*                          base type is a WrapLattice and whose predicate's  *)
(*                          canonical pred_key is a setJoinPred.              *)
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

Local Open Scope classical_set_scope.
Local Open Scope order_scope.

Reserved Notation "'{' 'mclmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'mclmorphism'  U  ->  V }").
Reserved Notation "'{' 'jclmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'jclmorphism'  U  ->  V }").
Reserved Notation "'{' 'clmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'clmorphism'  U  ->  V }").

Definition set_f_is_glb d (T : porderType d) (set_f : set T -> T) :=
  forall S, lbound S (set_f S) /\ forall x, lbound S x -> x <= set_f S.

Definition set_f_is_lub d (T : porderType d) (set_f : set T -> T) :=
  forall S, ubound S (set_f S) /\ forall x, ubound S x -> set_f S <= x.

HB.mixin Record isCompleteLattice d T of Order.POrder d T := {
  set_meet : set T -> T;
  set_meet_is_glb : set_f_is_glb set_meet;
  set_join : set T -> T;
  set_join_is_lub : set_f_is_lub set_join;
}.

#[short(type="completeLatticeType")]
HB.structure Definition CompleteLattice d :=
  { T of Order.TBLattice d T & isCompleteLattice d T }.

HB.factory Record POrder_isCompleteLattice d T of Order.POrder d T := {
  set_meet : set T -> T;
  set_meet_is_glb : set_f_is_glb set_meet;
  set_join : set T -> T;
  set_join_is_lub : set_f_is_lub set_join;
}.

HB.builders Context d T of POrder_isCompleteLattice d T.

Lemma set_join_ub S : ubound S (set_join S).
Proof. exact: (set_join_is_lub S).1. Qed.

Lemma set_join_le_ub S x : ubound S x -> set_join S <= x.
Proof. exact: (set_join_is_lub S).2. Qed.

Lemma set_join1 x : set_join [set x] = x.
Proof.
by apply/le_anti; rewrite set_join_ub // andbT set_join_le_ub // ub_set1.
Qed.

Lemma set_joinUl S S' : ubound S (set_join (S `|` S')).
Proof.
move=> y Sy; have: (S `|` S') y by left.
move: y {Sy}; exact: set_join_ub.
Qed.

Lemma set_joinUr S S' : ubound S' (set_join (S `|` S')).
Proof. rewrite setUC; exact: set_joinUl. Qed.

Lemma set_joinU_ge_l S S' : set_join S <= set_join (S `|` S').
Proof. exact/set_join_le_ub/set_joinUl. Qed.

Lemma set_joinU_ge_r S S' : set_join S' <= set_join (S `|` S').
Proof. exact/set_join_le_ub/set_joinUr. Qed.

Lemma set_joinU_le S S' x :
  set_join S <= x -> set_join S' <= x -> set_join (S `|` S') <= x.
Proof.
move=> jSx jS'x; apply: set_join_le_ub => y [] Sy.
- move: jSx; exact/le_trans/set_join_ub.
- move: jS'x; exact/le_trans/set_join_ub.
Qed.

Lemma set_meet_lb S : lbound S (set_meet S).
Proof. exact: (set_meet_is_glb S).1. Qed.

Lemma set_meet_ge_lb S x : lbound S x -> x <= set_meet S.
Proof. exact: (set_meet_is_glb S).2. Qed.

Lemma set_meet1 x : set_meet [set x] = x.
Proof. by apply/le_anti; rewrite set_meet_lb //= set_meet_ge_lb // lb_set1. Qed.

Lemma set_meetUl S S' : lbound S (set_meet (S `|` S')).
Proof.
move=> y Sy; have: (S `|` S') y by left.
move: y {Sy}; exact: set_meet_lb.
Qed.

Lemma set_meetUr S S' : lbound S' (set_meet (S `|` S')).
Proof. rewrite setUC; exact: set_meetUl. Qed.

Lemma set_meetU_le_l S S' : set_meet (S `|` S') <= set_meet S.
Proof. exact/set_meet_ge_lb/set_meetUl. Qed.

Lemma set_meetU_le_r S S' : set_meet (S `|` S') <= set_meet S'.
Proof. exact/set_meet_ge_lb/set_meetUr. Qed.

Lemma set_meetU_ge S S' x :
  x <= set_meet S -> x <= set_meet S' -> x <= set_meet (S `|` S').
Proof.
move=> xmS xmS'; apply: set_meet_ge_lb => y [] Sy.
- exact/(le_trans xmS)/set_meet_lb.
- exact/(le_trans xmS')/set_meet_lb.
Qed.

Definition join x y := set_join [set x; y].

Definition meet x y := set_meet [set x; y].

Lemma join_ge_l x y : x <= join x y.
Proof. move: (@set_joinUl (set1 x) (set1 y)); rewrite -ubP; exact. Qed.

Lemma join_ge_r x y : y <= join x y.
Proof. move: (@set_joinUr (set1 x) (set1 y)); rewrite -ubP; exact. Qed.

Lemma join_le x y z : x <= z -> y <= z -> join x y <= z.
Proof. by move=> Hx Hy; apply: set_joinU_le; rewrite set_join1. Qed.

Lemma set_joinU S S' : set_join (setU S S') = join (set_join S) (set_join S').
Proof.
apply/le_anti; rewrite set_joinU_le ?join_ge_l ?join_ge_r//.
by rewrite join_le ?set_joinU_ge_l ?set_joinU_ge_r.
Qed.

Lemma meet_le_l x y : meet x y <= x.
Proof. move: (@set_meetUl (set1 x) (set1 y)); rewrite -lbP; exact. Qed.

Lemma meet_le_r x y : meet x y <= y.
Proof. move: (@set_meetUr (set1 x) (set1 y)); rewrite -lbP; exact. Qed.

Lemma meet_ge x y z : z <= x -> z <= y -> z <= meet x y.
Proof. by move=> Hx Hy; apply: set_meetU_ge; rewrite set_meet1. Qed.

Lemma set_meetU S S' : set_meet (setU S S') = meet (set_meet S) (set_meet S').
Proof.
apply/le_anti; rewrite meet_ge ?set_meetU_le_l ?set_meetU_le_r//.
by rewrite set_meetU_ge ?meet_le_l ?meet_le_r.
Qed.

Lemma joinC : commutative join.
Proof. by move=> x y; rewrite /join setUC. Qed.

Lemma meetC : commutative meet.
Proof. by move=> x y; rewrite /meet setUC. Qed.

Lemma joinA : associative join.
Proof.
by move=> x y z; rewrite -{1}[x]set_join1 -set_joinU setUA set_joinU set_join1.
Qed.

Lemma meetA : associative meet.
Proof.
by move=> x y z; rewrite -{1}[x]set_meet1 -set_meetU setUA set_meetU set_meet1.
Qed.

Lemma joinK y x : meet x (join x y) = x.
Proof. by apply/le_anti; rewrite meet_le_l meet_ge ?join_ge_l. Qed.

Lemma meetK y x : join x (meet x y) = x.
Proof. by apply/le_anti; rewrite join_ge_l join_le ?meet_le_l. Qed.

Lemma meet_le x y : (x <= y) = (meet x y == x).
Proof.
apply/idP/idP => [Hxy|/eqP <-]; [|exact: meet_le_r].
by apply/eqP/le_anti; rewrite meet_le_l meet_ge.
Qed.

HB.instance Definition _ := Order.POrder_isLattice.Build d T
  meetC joinC meetA joinA joinK meetK meet_le.

Lemma le0x x : set_join set0 <= x.
Proof. exact: set_join_le_ub. Qed.

HB.instance Definition _ := Order.hasBottom.Build d T le0x.

Lemma lex1 x : x <= set_meet set0.
Proof. exact: set_meet_ge_lb. Qed.

HB.instance Definition _ := Order.hasTop.Build d T lex1.

HB.instance Definition _ := isCompleteLattice.Build d T
  set_meet_is_glb set_join_is_lub.

HB.end.

HB.factory Record POrder_isMeetCompleteLattice d T of Order.POrder d T := {
  set_meet : set T -> T;
  set_meet_is_glb : set_f_is_glb set_meet;
}.

HB.builders Context d T of POrder_isMeetCompleteLattice d T.
Definition set_join S := set_meet (ubound S).
Lemma set_join_is_lub : set_f_is_lub set_join.
Proof.
move=> B; split; [|exact: (set_meet_is_glb _).1].
by move=> x Bx;  apply: (set_meet_is_glb _).2; move=> y; apply.
Qed.
HB.instance Definition _ := POrder_isCompleteLattice.Build d T
  set_meet_is_glb set_join_is_lub.
HB.end.

HB.factory Record POrder_isJoinCompleteLattice d T of Order.POrder d T := {
  set_join : set T -> T;
  set_join_is_lub : set_f_is_lub set_join;
}.

HB.builders Context d T of POrder_isJoinCompleteLattice d T.
Definition set_meet S := set_join (lbound S).
Lemma set_meet_is_glb : set_f_is_glb set_meet.
Proof.
move=> B; split; [|exact: (set_join_is_lub _).1].
by move=> x Bx;  apply: (set_join_is_lub _).2; move=> y; apply.
Qed.
HB.instance Definition _ := POrder_isCompleteLattice.Build d T
  set_meet_is_glb set_join_is_lub.
HB.end.

Section CompleteLatticeTheory.

Variables (d : unit) (L : completeLatticeType d).

Implicit Types S : set L.
Implicit Types x : L.

Lemma set_join_ub S : ubound S (set_join S).
Proof. exact: (set_join_is_lub S).1. Qed.

Lemma set_join_le_ub S x : ubound S x -> set_join S <= x.
Proof. exact: (set_join_is_lub S).2. Qed.

Lemma set_join_le_incl S S' : S `<=` S' -> set_join S <= set_join S'.
Proof. move=> SS'; apply: set_join_le_ub => x Sx; exact/set_join_ub/SS'. Qed.

Lemma set_join_unique S x :
  ubound S x -> (forall y, ubound S y -> x <= y) -> x = set_join S.
Proof.
move=> xub xlub; apply/le_anti; rewrite set_join_le_ub // andbT.
exact/xlub/set_join_ub.
Qed.

Lemma set_join1 x : set_join [set x] = x.
Proof.
apply/le_anti; rewrite set_join_ub // andbT.
by rewrite set_join_le_ub ?ub_set1.
Qed.

Lemma set_joinUl S S' : ubound S (set_join (S `|` S')).
Proof.
move=> y Sy; have: (S `|` S') y by left.
move: y {Sy}; exact: set_join_ub.
Qed.

Lemma set_joinUr S S' : ubound S' (set_join (S `|` S')).
Proof. rewrite setUC; exact: set_joinUl. Qed.

Lemma set_joinU_ge_l S S' : set_join S <= set_join (S `|` S').
Proof. exact/set_join_le_ub/set_joinUl. Qed.

Lemma set_joinU_ge_r S S' : set_join S' <= set_join (S `|` S').
Proof. exact/set_join_le_ub/set_joinUr. Qed.

Lemma set_joinU_le S S' x :
  set_join S <= x -> set_join S' <= x -> set_join (S `|` S') <= x.
Proof.
move=> jSx jS'x; apply: set_join_le_ub => y [] Sy.
- move: jSx; exact/le_trans/set_join_ub.
- move: jS'x; exact/le_trans/set_join_ub.
Qed.

Lemma set_meet_lb S : lbound S (set_meet S).
Proof. exact: (set_meet_is_glb S).1. Qed.

Lemma set_meet_ge_lb S x : lbound S x -> x <= set_meet S.
Proof. exact: (set_meet_is_glb S).2. Qed.

Lemma set_meet_le_incl S S' : S `<=` S' -> set_meet S' <= set_meet S.
Proof. move=> SS'; apply: set_meet_ge_lb => x Sx; exact/set_meet_lb/SS'. Qed.

Lemma set_meet_unique S x :
  lbound S x -> (forall y, lbound S y -> y <= x) -> x = set_meet S.
Proof.
move=> xlb xglb; apply/le_anti; rewrite set_meet_ge_lb //=.
exact/xglb/set_meet_lb.
Qed.

Lemma set_meet1 x : set_meet [set x] = x.
Proof. by apply/le_anti; rewrite set_meet_lb // set_meet_ge_lb ?lb_set1. Qed.

Lemma set_meetUl S S' : lbound S (set_meet (S `|` S')).
Proof.
move=> y Sy; have: (S `|` S') y by left.
move: y {Sy}; exact: set_meet_lb.
Qed.

Lemma set_meetUr S S' : lbound S' (set_meet (S `|` S')).
Proof. rewrite setUC; exact: set_meetUl. Qed.

Lemma set_meetU_le_l S S' : set_meet (S `|` S') <= set_meet S.
Proof. exact/set_meet_ge_lb/set_meetUl. Qed.

Lemma set_meetU_le_r S S' : set_meet (S `|` S') <= set_meet S'.
Proof. exact/set_meet_ge_lb/set_meetUr. Qed.

Lemma set_meetU_ge S S' x :
  x <= set_meet S -> x <= set_meet S' -> x <= set_meet (S `|` S').
Proof.
move=> xmS xmS'; apply: set_meet_ge_lb => y [] Sy.
- exact/(le_trans xmS)/set_meet_lb.
- exact/(le_trans xmS')/set_meet_lb.
Qed.

Lemma set_joinT : set_join setT = 1%O :> L.
Proof. by apply/le_anti; rewrite lex1 set_join_ub. Qed.

Lemma set_join0 : set_join set0 = 0%O :> L.
Proof. by apply/le_anti; rewrite le0x set_join_le_ub. Qed.

Lemma set_meetT : set_meet setT = 0%O :> L.
Proof. by apply/le_anti; rewrite le0x set_meet_lb. Qed.

Lemma set_meet0 : set_meet set0 = 1%O :> L.
Proof. by apply/le_anti; rewrite lex1 set_meet_ge_lb. Qed.

Lemma set_join2 x y : set_join [set x; y] = x `|` y.
Proof.
apply/le_anti; rewrite set_joinU_le ?set_join1 ?leUl ?leUr//.
rewrite leUx -[leLHS](set_join1 x) set_joinU_ge_l /=.
by rewrite -[leLHS](set_join1 y) set_joinU_ge_r.
Qed.

Lemma set_meet2 x y : set_meet [set x; y] = x `&` y.
Proof.
apply/le_anti; rewrite set_meetU_ge ?set_meet1 ?leIl ?leIr//.
rewrite lexI -[leRHS](set_meet1 x) set_meetU_le_l /=.
by rewrite -[leRHS](set_meet1 y) set_meetU_le_r.
Qed.

Lemma set_joinU S S' : set_join (S `|` S') = set_join S `|` set_join S'.
Proof.
apply/le_anti; rewrite set_joinU_le ?leUl ?leUr//.
by rewrite leUx set_joinU_ge_l set_joinU_ge_r.
Qed.

Lemma set_meetU S S' : set_meet (S `|` S') = set_meet S `&` set_meet S'.
Proof.
apply/le_anti; rewrite set_meetU_ge ?leIl ?leIr//.
by rewrite lexI set_meetU_le_l set_meetU_le_r.
Qed.

Lemma set_meet_ubound S : set_meet (ubound S) = set_join S.
Proof.
apply/esym/set_meet_unique; [exact: set_join_le_ub|].
by move=> y; apply; apply: set_join_ub.
Qed.

Lemma set_join_lbound S : set_join (lbound S) = set_meet S.
Proof.
apply/esym/set_join_unique; [exact: set_meet_ge_lb|].
by move=> y; apply; apply: set_meet_lb.
Qed.

Section ClosedPredicates.

Variable S : {pred L}.

Definition set_meet_closed := forall (B : set L), B `<=` S -> set_meet B \in S.

Definition set_join_closed := forall (B : set L), B `<=` S -> set_join B \in S.

End ClosedPredicates.

End CompleteLatticeTheory.

Definition set_meet_morphism d (L : completeLatticeType d)
    d' (L' : completeLatticeType d') (f : L -> L') : Prop :=
  forall S, f (set_meet S) = set_meet (f @` S).

Definition set_join_morphism d (L : completeLatticeType d)
    d' (L' : completeLatticeType d') (f : L -> L') : Prop :=
  forall S, f (set_join S) = set_join (f @` S).

HB.mixin Record isSetMeetMorphism d (L : completeLatticeType d)
    d' (L' : completeLatticeType d') (apply : L -> L') := {
  omorphSM : set_meet_morphism apply;
}.

HB.mixin Record isSetJoinMorphism d (L : completeLatticeType d)
    d' (L' : completeLatticeType d') (apply : L -> L') := {
  omorphSJ : set_join_morphism apply;
}.

#[infer(L,L')]
HB.structure Definition MeetCompleteLatticeMorphism
    d (L : completeLatticeType d) d' (L' : completeLatticeType d') :=
  {f of isSetMeetMorphism d L d' L' f & @Order.MeetLatticeMorphism d L d' L' f
   & @Order.TLatticeMorphism d L d' L' f}.

#[infer(L,L')]
HB.structure Definition JoinCompleteLatticeMorphism
    d (L : completeLatticeType d) d' (L' : completeLatticeType d') :=
  {f of isSetJoinMorphism d L d' L' f & @Order.JoinLatticeMorphism d L d' L' f
   & @Order.BLatticeMorphism d L d' L' f}.

#[infer(L,L')]
HB.structure Definition CompleteLatticeMorphism
    d (L : completeLatticeType d) d' (L' : completeLatticeType d') :=
  {f of @MeetCompleteLatticeMorphism d L d' L' f
   & @JoinCompleteLatticeMorphism d L d' L' f}.

HB.factory Record isMeetCompleteLatticeMorphism d (L : completeLatticeType d)
    d' (L' : completeLatticeType d') (apply : L -> L')
    of @Order.OrderMorphism d L d' L' apply := {
  omorphSM : set_meet_morphism apply;
}.

HB.builders Context d L d' L' f of isMeetCompleteLatticeMorphism d L d' L' f.
Lemma omorphI : Order.meet_morphism f.
Proof. by move=> x y; rewrite -!set_meet2 omorphSM !image_setU !image_set1. Qed.
HB.instance Definition _ := Order.isMeetLatticeMorphism.Build d L d' L' f
  omorphI.
Lemma omorph1 : f 1 = 1.
Proof. by rewrite -[1 in LHS]set_meet0 omorphSM image_set0 set_meet0. Qed.
HB.instance Definition _ := Order.isTLatticeMorphism.Build d L d' L' f omorph1.
HB.instance Definition _ := isSetMeetMorphism.Build d L d' L' f omorphSM.
HB.end.

HB.factory Record isJoinCompleteLatticeMorphism d (L : completeLatticeType d)
    d' (L' : completeLatticeType d') (apply : L -> L')
    of @Order.OrderMorphism d L d' L' apply := {
  omorphSJ : set_join_morphism apply;
}.

HB.builders Context d L d' L' f of isJoinCompleteLatticeMorphism d L d' L' f.
Lemma omorphU : Order.join_morphism f.
Proof. by move=> x y; rewrite -!set_join2 omorphSJ !image_setU !image_set1. Qed.
HB.instance Definition _ := Order.isJoinLatticeMorphism.Build d L d' L' f
  omorphU.
Lemma omorph0 : f 0 = 0.
Proof. by rewrite -[0 in LHS]set_join0 omorphSJ image_set0 set_join0. Qed.
HB.instance Definition _ := Order.isBLatticeMorphism.Build d L d' L' f omorph0.
HB.instance Definition _ := isSetJoinMorphism.Build d L d' L' f omorphSJ.
HB.end.

HB.factory Record isCompleteLatticeMorphism d (L : completeLatticeType d)
    d' (L' : completeLatticeType d') (apply : L -> L')
    of @Order.OrderMorphism d L d' L' apply := {
  omorphSM : set_meet_morphism apply;
  omorphSJ : set_join_morphism apply;
}.

HB.builders Context d L d' L' f of isCompleteLatticeMorphism d L d' L' f.
HB.instance Definition _ := isMeetCompleteLatticeMorphism.Build d L d' L' f
  omorphSM.
HB.instance Definition _ := isJoinCompleteLatticeMorphism.Build d L d' L' f
  omorphSJ.
HB.end.

Notation "{ 'mclmorphism' T -> T' }" :=
  (MeetCompleteLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "{ 'jclmorphism' T -> T' }" :=
  (JoinCompleteLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "{ 'clmorphism' T -> T' }" :=
  (CompleteLatticeMorphism.type _ T%type _ T'%type) : type_scope.
Notation "[ 'mclmorphism' 'of' f 'as' g ]" :=
  (MeetCompleteLatticeMorphism.clone _ _ _ _ f%function g)
  (at level 0, format "[ 'mclmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'mclmorphism' 'of' f ]" :=
  (MeetCompleteLatticeMorphism.clone _ _ _ _ f%function _)
  (at level 0, format "[ 'mclmorphism'  'of'  f ]") : form_scope.
Notation "[ 'jclmorphism' 'of' f 'as' g ]" :=
  (JoinCompleteLatticeMorphism.clone _ _ _ _ f%function g)
  (at level 0, format "[ 'jclmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'jclmorphism' 'of' f ]" :=
  (JoinCompleteLatticeMorphism.clone _ _ _ _ f%function _)
  (at level 0, format "[ 'jclmorphism'  'of'  f ]") : form_scope.
Notation "[ 'clmorphism' 'of' f 'as' g ]" :=
  (CompleteLatticeMorphism.clone _ _ _ _ f%function g)
  (at level 0, format "[ 'clmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'clmorphism' 'of' f ]" :=
  (CompleteLatticeMorphism.clone _ _ _ _ f%function _)
  (at level 0, format "[ 'clmorphism'  'of'  f ]") : form_scope.

Arguments omorphSM {d L d' L'} _.
Arguments omorphSJ {d L d' L'} _.

Section CompleteLatticeMorphismTheory.

Section IdCompFun.

Variables (d : unit) (T : completeLatticeType d).
Variables (d' : unit) (T' : completeLatticeType d').
Variables (d'' : unit) (T'' : completeLatticeType d'').

Section MeetCompFun.

Variables (f : {mclmorphism T' -> T''}) (g : {mclmorphism T -> T'}).

Fact idfun_is_set_meet_morphism : set_meet_morphism (@idfun T).
Proof. by move=> B; rewrite image_id. Qed.
#[export]
HB.instance Definition _ := isMeetCompleteLatticeMorphism.Build d T d T idfun
  idfun_is_set_meet_morphism.

Fact comp_is_meet_morphism : set_meet_morphism (f \o g).
Proof. by move=> B; rewrite /= !omorphSM image_comp. Qed.
#[export]
HB.instance Definition _ :=
  isMeetCompleteLatticeMorphism.Build d T d'' T'' (f \o g)
    comp_is_meet_morphism.

End MeetCompFun.

Section JoinCompFun.

Variables (f : {jclmorphism T' -> T''}) (g : {jclmorphism T -> T'}).

Fact idfun_is_set_join_morphism : set_join_morphism (@idfun T).
Proof. by move=> B; rewrite image_id. Qed.
#[export]
HB.instance Definition _ := isJoinCompleteLatticeMorphism.Build d T d T idfun
  idfun_is_set_join_morphism.

Fact comp_is_set_join_morphism : set_join_morphism (f \o g).
Proof. by move=> B; rewrite /= !omorphSJ image_comp. Qed.
#[export]
HB.instance Definition _ :=
  isJoinCompleteLatticeMorphism.Build d T d'' T'' (f \o g)
    comp_is_set_join_morphism.

End JoinCompFun.

End IdCompFun.

End CompleteLatticeMorphismTheory.

(* Mixins for stability properties *)

HB.mixin Record isSetMeetClosed d (T : completeLatticeType d)
    (S : {pred T}) := {
  opredSM : set_meet_closed S;
}.

HB.mixin Record isSetJoinClosed d (T : completeLatticeType d)
    (S : {pred T}) := {
  opredSJ : set_join_closed S;
}.

(* Structures for stability properties *)

#[infer(T), short(type="meetCompleteLatticeClosed")]
HB.structure Definition MeetCompleteLatticeClosed d T :=
  {S of isSetMeetClosed d T S & @Order.TMeetLatticeClosed d T S}.

#[infer(T), short(type="joinCompleteLatticeClosed")]
HB.structure Definition JoinCompleteLatticeClosed d T :=
  {S of isSetJoinClosed d T S & @Order.BJoinLatticeClosed d T S}.

#[infer(T), short(type="completeLatticeClosed")]
HB.structure Definition CompleteLatticeClosed d T :=
  {S of @MeetCompleteLatticeClosed d T S & @JoinCompleteLatticeClosed d T S}.

(* Factories for stability properties *)

HB.factory Record isMeetCompleteLatticeClosed d (T : completeLatticeType d)
    (S : {pred T}) := {
  opredSM : set_meet_closed S;
}.

HB.builders Context d T S of isMeetCompleteLatticeClosed d T S.
Lemma opred1 : 1 \in S. Proof. by rewrite -set_meet0 opredSM. Qed.
HB.instance Definition _ := Order.isTLatticeClosed.Build d T S opred1.
Lemma opredI : meet_closed S.
Proof. by move=> x y xS yS; rewrite -set_meet2 opredSM// => _ [] ->. Qed.
HB.instance Definition _ := Order.isMeetLatticeClosed.Build d T S opredI.
HB.instance Definition _ := isSetMeetClosed.Build d T S opredSM.
HB.end.

HB.factory Record isJoinCompleteLatticeClosed d (T : completeLatticeType d)
    (S : {pred T}) := {
  opredSJ : set_join_closed S;
}.

HB.builders Context d T S of isJoinCompleteLatticeClosed d T S.
Lemma opred0 : 0 \in S. Proof. by rewrite -set_join0 opredSJ. Qed.
HB.instance Definition _ := Order.isBLatticeClosed.Build d T S opred0.
Lemma opredU : join_closed S.
Proof. by move=> x y xS yS; rewrite -set_join2 opredSJ// => _ [] ->. Qed.
HB.instance Definition _ := Order.isJoinLatticeClosed.Build d T S opredU.
HB.instance Definition _ := isSetJoinClosed.Build d T S opredSJ.
HB.end.

HB.factory Record isCompleteLatticeClosed d (T : completeLatticeType d)
    (S : {pred T}) := {
  opredSM : set_meet_closed S;
  opredSJ : set_join_closed S;
}.

HB.builders Context d T S of isCompleteLatticeClosed d T S.
HB.instance Definition _ := isMeetCompleteLatticeClosed.Build d T S opredSM.
HB.instance Definition _ := isJoinCompleteLatticeClosed.Build d T S opredSJ.
HB.end.

Arguments opredSM {d T} _.
Arguments opredSJ {d T} _.

HB.mixin Record isMeetSubCompleteLattice d (T : completeLatticeType d)
    (S : pred T) d' U of Sub T S U & CompleteLattice d' U := {
  valSM_subproof : set_meet_morphism (val : U -> T);
}.

HB.mixin Record isJoinSubCompleteLattice d (T : completeLatticeType d)
    (S : pred T) d' U of Sub T S U & CompleteLattice d' U := {
  valSJ_subproof : set_join_morphism (val : U -> T);
}.

#[short(type="subPOrderCompleteLattice")]
HB.structure Definition SubPOrderCompleteLattice d (T : completeLatticeType d)
  S d' := { U of @Order.SubPOrder d T S d' U & CompleteLattice d' U }.

#[short(type="meetSubCompleteLattice")]
HB.structure Definition MeetSubCompleteLattice d (T : completeLatticeType d) S
    d' :=
  { U of @Order.TMeetSubLattice d T S d' U & CompleteLattice d' U
    & isMeetSubCompleteLattice d T S d' U }.

#[short(type="joinSubCompleteLattice")]
HB.structure Definition JoinSubCompleteLattice d (T : completeLatticeType d) S
    d' :=
  { U of @Order.BJoinSubLattice d T S d' U & CompleteLattice d' U
    & isJoinSubCompleteLattice d T S d' U }.

#[short(type="subCompleteLattice")]
HB.structure Definition SubCompleteLattice d (T : completeLatticeType d) S
    d' :=
  { U of @MeetSubCompleteLattice d T S d' U
    & @JoinSubCompleteLattice d T S d' U }.

#[export]
HB.instance Definition _ (d : unit) (T : completeLatticeType d) (S : pred T)
    d' (U : MeetSubCompleteLattice.type S d') :=
  isMeetCompleteLatticeMorphism.Build d' U d T val valSM_subproof.

#[export]
HB.instance Definition _ (d : unit) (T : completeLatticeType d) (S : pred T)
    d' (U : JoinSubCompleteLattice.type S d') :=
  isJoinCompleteLatticeMorphism.Build d' U d T val valSJ_subproof.

HB.factory Record SubPOrder_isMeetSubCompleteLattice d
    (T : completeLatticeType d) S d' U of @Order.SubPOrder d T S d' U := {
  opredSM_subproof : set_meet_closed S;
}.

HB.builders Context d T S d' U of SubPOrder_isMeetSubCompleteLattice d T S d' U.

HB.instance Definition _ := isMeetCompleteLatticeClosed.Build d T S
  opredSM_subproof.

Lemma opredSM (B : set U) : set_meet (val @` B) \in S.
Proof. by apply: opredSM => _ [y By] <- /=; apply: valP. Qed.

Let inU v Sv : U := eqtype.sub v Sv.
Let set_meetU (B : set U) := inU (opredSM B).

Lemma set_meetU_is_glb : set_f_is_glb set_meetU.
Proof.
move=> B; split.
- by move=> x Bx; rewrite leEsub subK set_meet_lb//; exists x.
- move=> x ubx; rewrite leEsub subK set_meet_ge_lb// => _ [y By <-].
  by rewrite -leEsub ubx.
Qed.

HB.instance Definition _ := POrder_isMeetCompleteLattice.Build d' U
  set_meetU_is_glb.

Lemma val1 : (val : U -> T) 1 = 1.
Proof. by rewrite subK image_set0 set_meet0. Qed.
HB.instance Definition _ := Order.isTSubLattice.Build d T S d' U val1.

Lemma valI : Order.meet_morphism (val : U -> T).
Proof. by move=> x y; rewrite subK !image_setU !image_set1 set_meet2. Qed.
HB.instance Definition _ := Order.isMeetSubLattice.Build d T S d' U valI.

Lemma valSM : set_meet_morphism (val : U -> T).
Proof. by move=> B; rewrite subK. Qed.
HB.instance Definition _ := isMeetSubCompleteLattice.Build d T S d' U valSM.

HB.end.

HB.factory Record SubChoice_isMeetSubCompleteLattice d
    (T : completeLatticeType d) S (d' : unit) U of SubChoice T S U := {
  opredSM_subproof : set_meet_closed S;
}.

HB.builders Context d T S d' U of SubChoice_isMeetSubCompleteLattice d T S d' U.
HB.instance Definition _ := Order.SubChoice_isSubPOrder.Build d T S d' U.
HB.instance Definition _ := SubPOrder_isMeetSubCompleteLattice.Build d T S d' U
  opredSM_subproof.
HB.end.

HB.factory Record SubPOrder_isJoinSubCompleteLattice d
    (T : completeLatticeType d) S d' U of @Order.SubPOrder d T S d' U := {
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d T S d' U of SubPOrder_isJoinSubCompleteLattice d T S d' U.

HB.instance Definition _ := isJoinCompleteLatticeClosed.Build d T S
  opredSJ_subproof.

Lemma opredSJ (B : set U) : set_join (val @` B) \in S.
Proof. by apply: opredSJ => _ [y By] <- /=; apply: valP. Qed.

Let inU v Sv : U := eqtype.sub v Sv.
Let set_joinU (B : set U) := inU (opredSJ B).

Lemma set_joinU_is_lub : set_f_is_lub set_joinU.
Proof.
move=> B; split.
- by move=> x Bx; rewrite leEsub subK set_join_ub//; exists x.
- move=> x ubx; rewrite leEsub subK set_join_le_ub// => _ [y By <-].
  by rewrite -leEsub ubx.
Qed.

HB.instance Definition _ := POrder_isJoinCompleteLattice.Build d' U
  set_joinU_is_lub.

Lemma val0 : (val : U -> T) 0 = 0.
Proof. by rewrite subK image_set0 set_join0. Qed.
HB.instance Definition _ := Order.isBSubLattice.Build d T S d' U val0.

Lemma valU : Order.join_morphism (val : U -> T).
Proof. by move=> x y; rewrite subK !image_setU !image_set1 set_join2. Qed.
HB.instance Definition _ := Order.isJoinSubLattice.Build d T S d' U valU.

Lemma valSJ : set_join_morphism (val : U -> T).
Proof. by move=> B; rewrite subK. Qed.
HB.instance Definition _ := isJoinSubCompleteLattice.Build d T S d' U valSJ.

HB.end.

HB.factory Record SubChoice_isJoinSubCompleteLattice d
    (T : completeLatticeType d) S (d' : unit) U of SubChoice T S U := {
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d T S d' U of SubChoice_isJoinSubCompleteLattice d T S d' U.
HB.instance Definition _ := Order.SubChoice_isSubPOrder.Build d T S d' U.
HB.instance Definition _ := SubPOrder_isJoinSubCompleteLattice.Build d T S d' U
  opredSJ_subproof.
HB.end.

HB.factory Record SubPOrder_isSubCompleteLattice d
    (T : completeLatticeType d) S d' U of @Order.SubPOrder d T S d' U := {
  opredSM_subproof : set_meet_closed S;
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d T S d' U of SubPOrder_isSubCompleteLattice d T S d' U.

HB.instance Definition _ := isCompleteLatticeClosed.Build d T S
  opredSM_subproof opredSJ_subproof.

Lemma opredSM (B : set U) : set_meet (val @` B) \in S.
Proof. by apply: opredSM => _ [y By] <- /=; apply: valP. Qed.

Lemma opredSJ (B : set U) : set_join (val @` B) \in S.
Proof. by apply: opredSJ => _ [y By] <- /=; apply: valP. Qed.

Let inU v Sv : U := eqtype.sub v Sv.
Let set_meetU (B : set U) := inU (opredSM B).
Let set_joinU (B : set U) := inU (opredSJ B).

Lemma set_meetU_is_glb : set_f_is_glb set_meetU.
Proof.
move=> B; split.
- by move=> x Bx; rewrite leEsub subK set_meet_lb//; exists x.
- move=> x lbx; rewrite leEsub subK set_meet_ge_lb// => _ [y By <-].
  by rewrite -leEsub lbx.
Qed.

Lemma set_joinU_is_lub : set_f_is_lub set_joinU.
Proof.
move=> B; split.
- by move=> x Bx; rewrite leEsub subK set_join_ub//; exists x.
- move=> x ubx; rewrite leEsub subK set_join_le_ub// => _ [y By <-].
  by rewrite -leEsub ubx.
Qed.

HB.instance Definition _ := POrder_isCompleteLattice.Build d' U
  set_meetU_is_glb set_joinU_is_lub.

Lemma val0 : (val : U -> T) 0 = 0.
Proof. by rewrite subK image_set0 set_join0. Qed.
HB.instance Definition _ := Order.isBSubLattice.Build d T S d' U val0.

Lemma val1 : (val : U -> T) 1 = 1.
Proof. by rewrite subK image_set0 set_meet0. Qed.
HB.instance Definition _ := Order.isTSubLattice.Build d T S d' U val1.

Lemma valI : Order.meet_morphism (val : U -> T).
Proof. by move=> x y; rewrite subK !image_setU !image_set1 set_meet2. Qed.
HB.instance Definition _ := Order.isMeetSubLattice.Build d T S d' U valI.

Lemma valU : Order.join_morphism (val : U -> T).
Proof. by move=> x y; rewrite subK !image_setU !image_set1 set_join2. Qed.
HB.instance Definition _ := Order.isJoinSubLattice.Build d T S d' U valU.

Lemma valSM : set_meet_morphism (val : U -> T).
Proof. by move=> B; rewrite subK. Qed.
HB.instance Definition _ := isMeetSubCompleteLattice.Build d T S d' U valSM.

Lemma valSJ : set_join_morphism (val : U -> T).
Proof. by move=> B; rewrite subK. Qed.
HB.instance Definition _ := isJoinSubCompleteLattice.Build d T S d' U valSJ.

HB.end.

HB.factory Record SubChoice_isSubCompleteLattice d
    (T : completeLatticeType d) S (d' : unit) U of SubChoice T S U := {
  opredSM_subproof : set_meet_closed S;
  opredSJ_subproof : set_join_closed S;
}.

HB.builders Context d T S d' U of SubChoice_isSubCompleteLattice d T S d' U.
HB.instance Definition _ := Order.SubChoice_isSubPOrder.Build d T S d' U.
HB.instance Definition _ := SubPOrder_isSubCompleteLattice.Build d T S d' U
  opredSM_subproof opredSJ_subproof.
HB.end.

Notation "[ 'SubPOrder_isMeetSubCompleteLattice' 'of' U 'by' <: ]" :=
  (SubPOrder_isMeetSubCompleteLattice.Build _ _ _ _ U (opredSM _))
  (at level 0, format "[ 'SubPOrder_isMeetSubCompleteLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isMeetSubCompleteLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isMeetSubCompleteLattice.Build _ _ _ disp U (opredSM _))
  (at level 0, format "[ 'SubPOrder_isMeetSubCompleteLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isMeetSubCompleteLattice' 'of' U 'by' <: ]" :=
  (SubChoice_isMeetSubCompleteLattice.Build _ _ _ _ U (opredSM _))
  (at level 0, format "[ 'SubChoice_isMeetSubCompleteLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isMeetSubCompleteLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isMeetSubCompleteLattice.Build _ _ _ disp U (opredSM _))
  (at level 0, format "[ 'SubChoice_isMeetSubCompleteLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubPOrder_isJoinSubCompleteLattice' 'of' U 'by' <: ]" :=
  (SubPOrder_isJoinSubCompleteLattice.Build _ _ _ _ U (opredSJ _))
  (at level 0, format "[ 'SubPOrder_isJoinSubCompleteLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isJoinSubCompleteLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isJoinSubCompleteLattice.Build _ _ _ disp U (opredSJ _))
  (at level 0, format "[ 'SubPOrder_isJoinSubCompleteLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isJoinSubCompleteLattice' 'of' U 'by' <: ]" :=
  (SubChoice_isJoinSubCompleteLattice.Build _ _ _ _ U (opredSJ _))
  (at level 0, format "[ 'SubChoice_isJoinSubCompleteLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isJoinSubCompleteLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isJoinSubCompleteLattice.Build _ _ _ disp U (opredSJ _))
  (at level 0, format "[ 'SubChoice_isJoinSubCompleteLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubPOrder_isSubCompleteLattice' 'of' U 'by' <: ]" :=
  (SubPOrder_isSubCompleteLattice.Build _ _ _ _ U (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubPOrder_isSubCompleteLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isSubCompleteLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isSubCompleteLattice.Build _ _ _ disp U (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubPOrder_isSubCompleteLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubCompleteLattice' 'of' U 'by' <: ]" :=
  (SubChoice_isSubCompleteLattice.Build _ _ _ _ U (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isSubCompleteLattice'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubCompleteLattice' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubCompleteLattice.Build _ _ _ disp U (opredSM _) (opredSJ _))
  (at level 0, format "[ 'SubChoice_isSubCompleteLattice'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
