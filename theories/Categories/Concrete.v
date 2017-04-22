Require Import Morphisms Setoid Coq.Vectors.Fin ProofIrrelevance.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition One : Category :=
  Build_Category_from_Type
    {|
      cat_object := unit;
      cat_hom := fun _ _ => unit;
      cat_hom_equal := fun _ _ _ _ => True;
      cat_identity := fun _ => tt;
      cat_comp := fun _ _ _ _ _ => tt;
    |}.
Next Obligation.
  refine [hsetoid: fun _ _ _ _ _ _ => True].
  constructor.
  - trivial.
  - trivial.
  - trivial.
Defined.
Next Obligation.
  constructor.
  - auto.
  - auto.
  - auto.
Defined.
Next Obligation.
  constructor.
Defined.

Program Definition Product (C D : Category) : Category :=
  {|
    object := object C * object D;
    morphism := fun a b => @morphism C (fst a) (fst b) ** @morphism D (snd a) (snd b);
    identity := fun _ => Spair identity identity;
    compose := fun _ _ _ => [mapoid: fun gf => Spair (fst (fst gf) ∘ fst (snd gf)) (snd (fst gf) ∘ snd (snd gf))];
  |}.
Next Obligation.
  constructor.
  trivial.
  trivial.
Defined.
Next Obligation.
  exact (HSetoid_on_setoid (fun a b => @morphism C (fst a) (fst b) ** @morphism D (snd a) (snd b))).
Defined.
Next Obligation.
  simpl.
  unfold Proper, respectful.
  simpl.
  intros x y H.
  destruct H.
  destruct H, H0.
  split.
  - rewrite H, H0.
    reflexivity.
  - rewrite H1, H2.
    reflexivity.
Defined.
Next Obligation.
  constructor.
  - intros.
    constructor.
    + intro.
      apply heqex_extend_eq.
      exact H.
    + intro.
      generalize (heq_extending_eq H).
      intro.
      destruct H0.
      rewrite <- e.
      unfold Setoids.extend.
      destruct x.
      rewrite <- eq_rect_eq.
      rewrite <- eq_rect_eq.
      reflexivity.
  - simpl.
    intros.
    split.
    + apply associativity.
    + apply associativity.
  - simpl.
    intros.
    split.
    + apply left_identity.
    + apply left_identity.
  - simpl.
    intros.
    split.
    + apply right_identity.
    + apply right_identity.
Defined.

Infix "×" := Product (at level 50).

Program Definition Product_mediating {X Y C D} (f : Functor X C) (g : Functor Y D) : Functor (X × Y) (C × D)
  := [fmap: fun _ _ u => (| fmap f (fst u), fmap g (snd u) |) with fun (xy : X × Y) => (f (fst xy), g (snd xy)) : C × D ].
Next Obligation.
  unfold Proper, respectful.
  simpl.
  intros.
  destruct H.
  rewrite H, H0.
  split.
  reflexivity. reflexivity.
Defined.
Next Obligation.
  split.
  apply fmap_identity.
  apply fmap_identity.
Defined.
Next Obligation.
  split.
  apply fmap_compose.
  apply fmap_compose.
Defined.

Notation "⟨ProductF: f , g 'of' X , Y , C , D ⟩" := (@Product_mediating X Y C D f g).
Notation "⟨ProductF: f , g ⟩" := ⟨ProductF: f , g of _ , _ , _ , _⟩.


