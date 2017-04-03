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
      cat_hom_equal :=
        fun C _ F G => forall (fobj_eq : fobj F = fobj G),
          let shift := fun f => eq_subst fobj_eq (fmap F f) == fmap G f in
          (fobj F = fobj G) /\ (forall (fobj_eq : fobj F = fobj G), forall {a b : C} (f : a ⟶ b), fmap F f == fmap G f);
      cat_identity := @idFunctor;
      cat_comp := @compFunctor;
    |}.

