Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category Morphism Functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure Terminal {C : Category} :=
  {
    terminal : object C;
    is_terminal : forall x, ∃! (f : x ⟶ terminal) in C, True;
  }.

Structure Initial {C : Category} :=
  {
    initial : object C;
    is_initial : forall x, ∃! (f : initial ⟶ x) in C, True;
  }.

