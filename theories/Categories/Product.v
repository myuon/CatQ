Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Setoids Category Morphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition Product (C D : Category) : Category :=
  {|
    object := object C * object D;
    morphism := fun a b => @morphism C (fst a) (fst b) ** @morphism D (snd a) (snd b);
    identity := fun _ => Spair identity identity;
    compose := fun _ _ _ => {| mapping := fun gf => Spair (fst (fst gf) ∘ fst (snd gf)) (snd (fst gf) ∘ snd (snd gf)); |};
  |}.
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
  apply Build_Is_Category.
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

