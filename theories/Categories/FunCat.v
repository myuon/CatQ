Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
Require Import CatQ.Functors.Concrete.

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

Notation "[ C , D ]" := (FunCat C D).

Notation "PSh[ C ]" := (FunCat (opposite C) Setoids).

Program Definition const_lift {C J : Category} : Functor C [J,C] :=
  Build_Functor_from_Type
    {|
      funct_obj := fun a => (Δ[J](a) : object ([J,C]));
      funct_map :=
        fun a b f =>
          {|
            component := fun x => (f : hom (Δ[J](a) x) (Δ[J](b) x));
          |};
    |}.
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap Δ[J](b) f0 ∘ f
     =⟨ _ ⟩
      identity ∘ f
     =⟨ _ ⟩
      f
     =⟨ _ ⟩
      f ∘ identity
     =⟨ _ ⟩
      f ∘ fmap Δ[J](a) f0
     `end).

  - unfold const, fmap.
    simpl.
    reflexivity.
  - apply left_id_of.
  - rewrite right_id_of.
    reflexivity.
  - reflexivity.
Defined.
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Definition Δ {C J : Category} : Functor C ([J,C]) := const_lift.

  
