Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category Morphism Functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure Terminal {C : Category} :=
  {
    terminal : C;
    is_terminal : forall x, ∃! (f : x ⟶ terminal) in C, True;
  }.

Definition has_terminal (C : Category) := @Terminal C.

Structure Product {C : Category} (a b : C) :=
  {
    product : C;
    product_proj₁ : product ⟶ a;
    product_proj₂ : product ⟶ b;
    is_product :
      forall {c} (f : c ⟶ a) (g : c ⟶ b),
        ∃! (h : c ⟶ product) in C, product_proj₁ ∘ h == f /\ product_proj₂ ∘ h == g;
  }.

Definition has_product (C : Category) :=
  forall (a b : C), Product a b.

Structure sProduct {C : Category} (I : Type) (indexed : I → object C) :=
  {
    sproduct : C;
    sproduct_proj : forall i, sproduct ⟶ indexed i;
    is_sproduct :
      forall {c} (f : forall i, c ⟶ indexed i),
        ∃! (h : c ⟶ sproduct) in C, forall i, sproduct_proj i ∘ h == f i;
  }.

Definition has_sproduct (C : Category) :=
  forall {I} (indexed : I → object C), sProduct indexed.

Notation "⟨sproduct: f 'of' p ⟩" := (proj1 (is_sproduct p f)).

Structure Equalizer {C : Category} {a b : C} (f g : a ⟶ b) :=
  {
    equalizer : C;
    equalizing_map : equalizer ⟶ a;
    is_equalizer :
      forall {c} (f : c ⟶ a),
        ∃! (h : c ⟶ equalizer) in C, equalizing_map ∘ h == f;
  }.

Definition has_equalizer (C : Category) :=
  forall {a b : C} (f g : a ⟶ b), Equalizer f g.

Structure Initial {C : Category} :=
  {
    initial : C;
    is_initial : forall x, ∃! (f : initial ⟶ x) in C, True;
  }.

Definition has_initial (C : Category) := @Initial C.

Structure Coproduct {C : Category} (a b : C) :=
  {
    coproduct : C;
    coproduct_inj₁ : a ⟶ coproduct;
    coproduct_inj₂ : b ⟶ coproduct;
    is_coproduct :
      forall {c} (f : a ⟶ c) (g : b ⟶ c),
        ∃! (h : coproduct ⟶ c) in C, h ∘ coproduct_inj₁ == f /\ h ∘ coproduct_inj₂ == g;
  }.

Definition has_coproduct (C : Category) :=
  forall (a b : C), Coproduct a b.

Structure Coequalizer {C : Category} {a b : C} (f g : a ⟶ b) :=
  {
    coequalizer : C;
    coequalizing_map : b ⟶ coequalizer;
    is_coequalizer :
      forall {c} (f : b ⟶ c),
        ∃! (h : coequalizer ⟶ c) in C, h ∘ coequalizing_map == f;
  }.

Definition has_coequalizer (C : Category) :=
  forall {a b : C} (f g : a ⟶ b), Coequalizer f g.


