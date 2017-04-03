Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category Functor.

(* Nat *)
Class Is_Nat
      {C D : Category} (F G : Functor C D)
      (component : forall a, morphism (F a) (G a)) :=
  {
    naturality : forall {a b} {f : a ⟶ b},
                   fmap G f ∘ component a == component b ∘ fmap F f;
  }.

Structure Nat {C D : Category} (F G : Functor C D) :=
  {
    component :> forall a, morphism (F a) (G a);
    is_nat :> Is_Nat component;
  }.
Existing Instance is_nat.

Definition naturality_of {C D} {F G : Functor C D} (α : Nat F G) :
  forall {a b} {f : a ⟶ b},
    fmap G f ∘ α a == α b ∘ fmap F f
  := @naturality C D F G (component α) (is_nat α).

Program Definition idNat {C D : Category} (F : Functor C D) : Nat F F :=
  {|
    component := fun a => @identity D (fobj F a);
  |}.
Next Obligation.
  apply Build_Is_Nat.
  intros.
  setoid_rewrite (@right_identity D).
  setoid_rewrite (@left_identity D).
  - reflexivity.
  - destruct D. simpl. auto.
  - destruct D. simpl. auto.
Defined.

Program Definition compNat {C D : Category} {F G H : Functor C D} (β : Nat G H) (α : Nat F G) : Nat F H :=
  {|
    component := fun a => component β a ∘ component α a;
  |}.
Next Obligation.
  apply Build_Is_Nat.
  intros.
  exact
    (`begin
      fmap H f ∘ (β a ∘ α a)
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (fmap H f ∘ β a) ∘ α a
     =⟨ ltac: (rewrite (naturality_of β); reflexivity) ⟩
      (β b ∘ fmap G f) ∘ α a
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      β b ∘ (fmap G f ∘ α a)
     =⟨ ltac: (rewrite (naturality_of α); reflexivity) ⟩
      β b ∘ (α b ∘ fmap F f)
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (β b ∘ α b) ∘ fmap F f
     `end).
Defined.

