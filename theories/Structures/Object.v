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

Structure Product {C : Category} (a b : C) :=
  {
    product : C;
    product_proj₁ : product ⟶ a;
    product_proj₂ : product ⟶ b;
    is_product :
      forall {c} (f : c ⟶ a) (g : c ⟶ b),
        ∃! (h : c ⟶ product) in C, product_proj₁ ∘ h == f /\ product_proj₂ ∘ h == g;
  }.

Structure Equalizer {C : Category} {a b : C} (f g : a ⟶ b) :=
  {
    equalizer : C;
    equalizing_map : equalizer ⟶ a;
    is_equalizer :
      forall {c} (f : c ⟶ a),
        ∃! (h : c ⟶ equalizer) in C, equalizing_map ∘ h == f;
  }.

Structure Initial {C : Category} :=
  {
    initial : C;
    is_initial : forall x, ∃! (f : initial ⟶ x) in C, True;
  }.

Structure Coproduct {C : Category} (a b : C) :=
  {
    coproduct : C;
    coproduct_inj₁ : a ⟶ coproduct;
    coproduct_inj₂ : b ⟶ coproduct;
    is_coproduct :
      forall {c} (f : a ⟶ c) (g : b ⟶ c),
        ∃! (h : coproduct ⟶ c) in C, h ∘ coproduct_inj₁ == f /\ h ∘ coproduct_inj₂ == g;
  }.

Structure Coequalizer {C : Category} {a b : C} (f g : a ⟶ b) :=
  {
    coequalizer : C;
    coequalizing_map : b ⟶ coequalizer;
    is_coequalizer :
      forall {c} (f : b ⟶ c),
        ∃! (h : coequalizer ⟶ c) in C, h ∘ coequalizing_map == f;
  }.



