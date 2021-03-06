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
  to_Category
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
  [fmap: fun a b f => [Nat: fun x => (f : hom (Δ[J](a) x) (Δ[J](b) x))]
   with fun a => (Δ[J](a) : object ([J,C]))].
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap Δ[J](b) f0 ∘ f
     =⟨ hom_refl ⟩
      identity ∘ f
     =⟨ left_id_of ⟩
      f
     ↑⟨ right_id_of ⟩
      f ∘ identity
     =⟨ hom_refl ⟩
      f ∘ fmap Δ[J](a) f0
     `end).
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

Definition Δ {C J : Category} : Functor C [J,C] := const_lift.

Notation "Δ( f 'as' a 'to' b )" := (fmap Δ (f : a ⟶ b)).

  
