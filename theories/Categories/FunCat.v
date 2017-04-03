Require Import Morphisms.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category Functor Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition FunCat (C D : Category) : Category :=
  Build_Category_from_Type
    {|
      cat_object := Functor C D;
      cat_hom := Nat;
      cat_hom_equal := fun _ _ α β => forall A, component α A == component β A;
      cat_identity := idNat;
      cat_comp := fun _ _ _ => compNat;
    |}.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive.
    reflexivity.
  - unfold Symmetric.
    symmetry. apply H.
  - unfold Transitive.
    intros. rewrite H, H0. reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful.
  intros.
  unfold equality. simpl.
  rewrite H, H0.
  reflexivity.
Defined.
Next Obligation.
  apply assoc_of.
Defined.
Next Obligation.
  apply left_identity.
Defined.
Next Obligation.
  apply right_identity.
Defined.

Notation "[ C , D ]" := (FunCat C D) (at level 50).

Notation "PSh[ C ]" := (FunCat (opposite C) Setoids) (at level 50).
