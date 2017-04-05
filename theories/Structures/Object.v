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
    terminal_UMP : forall x, ∃! (f : x ⟶ terminal), True;
  }.



