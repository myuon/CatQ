Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure isomorphic {C : Category} (x y : C) :=
  {
    iso_right : hom x y;
    iso_left : hom y x;
    iso_on_left : iso_left ∘ iso_right == identity;
    iso_on_right : iso_right ∘ iso_left == identity;
  }.

Notation "A ≃ B" := (isomorphic A B) (at level 50).
Notation "A ≃ B 'at' C" := (@isomorphic C A B) (at level 50).

Definition exist_isomorphism {C : Category} (x y : C) : Prop
  := exists (f : x ⟶ y) (g : y ⟶ x), f ∘ g == identity /\ g ∘ f == identity.


