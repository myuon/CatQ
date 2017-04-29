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

Notation "[terminal: T 'by' prf ]" := (@Build_Terminal _ T prf).
Notation "[terminal: T ]" := [terminal: T by _].
Notation "⟨terminal: x 'of' p ⟩" := (proj1_sig (is_terminal p x)).

Lemma terminal_mediating_unique {C} (p : @Terminal C) {x} :
  forall (h : x ⟶ terminal p), h == ⟨terminal: x of p⟩.
Proof.
  intro.
  destruct (is_terminal p x).
  destruct u.
  simpl.
  symmetry.
  apply (e h).
  trivial.
Qed.
  
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

Notation "[product: P 'with' pr1 , pr2 'of' a , b 'by' prf ]" := (@Build_Product _ a b P pr1 pr2 prf).
Notation "[product: P 'with' pr1 , pr2 ]" := (@Build_Product _ _ _ P pr1 pr2 _).
Notation "[product: P ]" := (@Build_Product _ _ _ P _ _ _).
Notation "⟨product: f , g 'of' p ⟩" := (is_product p f g).

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

Notation "⟨sproduct: f 'of' p ⟩" := (proj1_sig (is_sproduct p f)).

Lemma sproduct_mediating_prop {C I indexed} (p : @sProduct C I indexed) {c} {f : forall i, c ⟶ indexed i} :
  forall i, sproduct_proj p i ∘ ⟨sproduct: f of p⟩ == f i.
Proof.
  intros.
  destruct p as [sprod proj is_sprod]; simpl.
  destruct (is_sprod c f); simpl.
  destruct u.
  exact (H i).
Qed.

Lemma sproduct_mediating_unique {C I indexed} (p : @sProduct C I indexed) {c} {f : forall i, c ⟶ indexed i} :
  forall h, (forall i, sproduct_proj p i ∘ h == f i) → (h == ⟨sproduct: f of p⟩).
Proof.
  intros.
  destruct p as [sprod proj is_sprod]; simpl.
  destruct (is_sprod c f); simpl.
  destruct u.
  symmetry.
  exact (H1 h H).
Qed.

Lemma sproduct_pointwise_equal {C I indexed} (p : @sProduct C I indexed) {c} {f g : c ⟶ sproduct p} :
  (forall i, sproduct_proj p i ∘ f == sproduct_proj p i ∘ g) → (f == g).
Proof.
  intros.
  rewrite (sproduct_mediating_unique (p:=p) (f:=fun i => sproduct_proj p i ∘ f) (h:=g)).
  - rewrite (sproduct_mediating_unique (p:=p) (f:=fun i => sproduct_proj p i ∘ f) (h:=f)).
    reflexivity.
    reflexivity.
  - symmetry.
    apply H.
Qed.

Notation "f [equalize] ( g , h )" := (g ∘ f == h ∘ f) (at level 0).

Class Is_Equalizer {C : Category} {a b : C} (f g : a ⟶ b)
      (equalizer : C) (equalizing_map : equalizer ⟶ a) :=
  {
    equalize_parallel: equalizing_map [equalize] (f,g);
    equalizer_UMP: 
      forall {c} (k : c ⟶ a),
        k [equalize] (f,g) → ∃! (h : c ⟶ equalizer) in C, equalizing_map ∘ h == k;
  }.

Structure Equalizer {C : Category} {a b : C} (f g : a ⟶ b) :=
  {
    equalizer : C;
    equalizing_map : equalizer ⟶ a;
    is_equalizer : @Is_Equalizer C a b f g equalizer equalizing_map;
  }.

Definition has_equalizer (C : Category) :=
  forall {a b : C} (f g : a ⟶ b), Equalizer f g.

Notation "⟨equalizer: f 'equalize' 'by' prf 'of' p ⟩" := (proj1_sig (@equalizer_UMP _ _ _ _ _ _ _ (is_equalizer p) _ f prf)).

Lemma equalizer_mediating_prop {C a b f g} (p : @Equalizer C a b f g) {c} {k : c ⟶ a} (kprop: k [equalize] (f,g)) :
  equalizing_map p ∘ ⟨equalizer: k equalize by kprop of p⟩ == k.
Proof.
  destruct p as [pob pmap peql]; simpl.
  destruct peql as [peql pUMP]; simpl.
  destruct (pUMP c k kprop).
  simpl.
  destruct u.
  exact H.
Qed.

Lemma equalizer_mediating_unique {C a b f g} (p : @Equalizer C a b f g) {c} {k : c ⟶ a} (kprop: k [equalize] (f,g)) :
  forall h, (equalizing_map p ∘ h == k) → h == ⟨equalizer: k equalize by kprop of p⟩.
Proof.
  destruct p as [pob pmap peql]; simpl.
  destruct peql as [peql pUMP]; simpl.
  destruct (pUMP c k kprop).
  simpl.
  intros.
  destruct u.
  symmetry.
  exact (H1 h H).
Qed.

Lemma equalizer_pointwise_equal {C a b f g} (p : @Equalizer C a b f g) {c} {s t : c ⟶ equalizer p} (sprop : (equalizing_map p ∘ s) [equalize] (f,g)) (tprop : (equalizing_map p ∘ t) [equalize] (f,g)) :
  (equalizing_map p ∘ s == equalizing_map p ∘ t) → (s == t).
Proof.
  intros.
  rewrite (@equalizer_mediating_unique _ _ _ _ _ p _ (equalizing_map p ∘ s) sprop t).
  - apply (@equalizer_mediating_unique _ _ _ _ _ p _ (equalizing_map p ∘ s) sprop s).
    reflexivity.
  - symmetry.
    apply H.
Qed.

Structure Initial {C : Category} :=
  {
    initial : C;
    is_initial : forall x, ∃! (f : initial ⟶ x) in C, True;
  }.

Notation "[initial: I 'by' prf ]" := (@Build_Initial _ I prf).
Notation "[initial: I ]" := [initial: I by _].
Notation "⟨initial: x 'of' p ⟩" := (proj1_sig (is_initial p x)).

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


