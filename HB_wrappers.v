From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

Fact dioid_display : unit. Proof. by []. Qed.

HB.mixin Record WrapChoice_of_TYPE T := {
  wrap_eqMixin : Equality.mixin_of T;
  wrap_choiceMixin : Choice.mixin_of T;
}.

HB.structure Definition WrapChoice := { T of WrapChoice_of_TYPE T }.

Coercion WrapChoice_to_Equality (T : WrapChoice.type) :=
  @Equality.Pack T wrap_eqMixin.
Canonical WrapChoice_to_Equality.
Coercion WrapChoice_to_Choice (T : WrapChoice.type) :=
  @Choice.Pack T (Choice.Class wrap_eqMixin wrap_choiceMixin).
Canonical WrapChoice_to_Choice.

HB.mixin Record WrapPOrder_of_WrapChoice T of WrapChoice T := {
  wrap_porderMixin : @Order.POrder.mixin_of T wrap_eqMixin;
}.

HB.structure Definition WrapPOrder :=
  { T of WrapChoice T & WrapPOrder_of_WrapChoice T }.

Coercion WrapPOrder_to_Equality (T : WrapPOrder.type) :=
  Eval hnf in [eqType of T for T].
Canonical WrapPOrder_to_Equality.
Coercion WrapPOrder_to_Choice (T : WrapPOrder.type) :=
  Eval hnf in [choiceType of T for T].
Canonical WrapPOrder_to_Choice.
Coercion WrapPOrder_to_POrder (T : WrapPOrder.type) :=
  @Order.POrder.pack
    T dioid_display (WrapChoice_to_Choice T) _ id wrap_porderMixin.
Canonical WrapPOrder_to_POrder.
