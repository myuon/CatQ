Require Import Morphisms.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category Functor Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition Cat : Category :=
  Build_Category_from_Type
    {|
      cat_object := Category;
      cat_hom := Functor;
      cat_hom_equal := fun _ _ => eqFunctor;
      cat_identity := @idFunctor;
      cat_comp := @compFunctor;
    |}.
Admit Obligations.


