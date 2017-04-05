Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
Require Import CatQ.Categories.Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition const {C D : Category} (a : C) : Functor D C :=
  Build_Functor_from_Type
    {|
      funct_obj := fun _ => a;
      funct_map := fun _ _ _ => identity;
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  rewrite left_id_of.
  reflexivity.
Defined.

Definition const_one {C : Category} (a : C) : Functor One C := const a.

Notation "Δ[ D ]( a )" := (@const _ D a) .
Notation "Δ( a )" := (const_one a) .

