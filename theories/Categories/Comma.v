Require Import Morphisms Setoid ProofIrrelevance.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat Cat.
Require Import CatQ.Yoneda.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure comma_pair {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) :=
  {
    csrc : object D₁;
    ctgt : object D₂;
    cedge : hom (K csrc) (L ctgt);
  }.

Notation "[comma_pair: e 'as' src 'to' tgt ]" := (@Build_comma_pair _ _ _ _ _ src tgt e).
Notation "[comma_pair: e ]" := [comma_pair: e as _ to _].

(* capture the equality of comma_pairs induced by hom equality in C *)
Definition eq_comma_pair {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (a b : comma_pair K L) :=
  { eq: csrc a = csrc b /\ ctgt a = ctgt b | extend (fobj_eq (proj1 eq)) (fobj_eq (proj2 eq)) (cedge a) == cedge b }.

Axiom comma_pair_equal : forall {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) {a b : comma_pair K L},
    eq_comma_pair a b → a = b.

Structure comma_morphism {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (a b : comma_pair K L) :=
  {
    esrc : hom (csrc a) (csrc b);
    etgt : hom (ctgt a) (ctgt b);
    is_comma_morphism : fmap L etgt ∘ (cedge a) == (cedge b) ∘ fmap K esrc;
  }.

Notation "[comma_map: f , g 'from' src 'to' tgt 'natural' 'by' prf ]" := (@Build_comma_morphism _ _ _ _ _ src tgt f g prf).
Notation "[comma_map: f , g 'from' src 'to' tgt ]" := [comma_map: f , g from src to tgt natural by _].
Notation "[comma_map: f , g 'natural' 'by' prf ]" := [comma_map: f , g from _ to _ natural by prf].
Notation "[comma_map: f , g ]" := [comma_map: f , g from _ to _].

Program Definition comma_id {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (a : comma_pair K L) : comma_morphism a a
  := [comma_map: identity, identity].
Next Obligation.
  rewrite fmap_identity.
  rewrite fmap_identity.
  rewrite right_id_of.
  rewrite left_id_of.
  reflexivity.
Defined.

Program Definition comma_comp {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (a b c : comma_pair K L) (g : comma_morphism b c) (f : comma_morphism a b) : comma_morphism a c
  := [comma_map: esrc g ∘ esrc f , etgt g ∘ etgt f ].
Next Obligation.
  exact
    (`begin
      fmap L (etgt g ∘ etgt f) ∘ cedge a
     =⟨ ltac: (rewrite fmap_compose; reflexivity) ⟩
      fmap L (etgt g) ∘ fmap L (etgt f) ∘ cedge a
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      fmap L (etgt g) ∘ (fmap L (etgt f) ∘ cedge a)
     =⟨ ltac: (rewrite (is_comma_morphism f); reflexivity) ⟩
      fmap L (etgt g) ∘ (cedge b ∘ fmap K (esrc f))
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (fmap L (etgt g) ∘ cedge b) ∘ fmap K (esrc f)
     =⟨ ltac: (rewrite (is_comma_morphism g); reflexivity) ⟩
      (cedge c ∘ fmap K (esrc g)) ∘ fmap K (esrc f)
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      cedge c ∘ (fmap K (esrc g) ∘ fmap K (esrc f))
     =⟨ ltac: (rewrite <- fmap_compose; reflexivity) ⟩
      cedge c ∘ fmap K (esrc g ∘ esrc f)
     `end).
Defined.

Definition comma_morphism_eq {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} (f g : comma_morphism a b) : Prop
  := esrc f == esrc g /\ etgt f == etgt g.

Instance esrc_proper {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} : Proper (comma_morphism_eq (a:=a) (b:=b) ==> @equality _) (fun f => esrc f).
Proof.
  unfold Proper, respectful, comma_morphism_eq.
  intros.
  destruct H.
  exact H.
Qed.

Instance etgt_proper {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} : Proper (comma_morphism_eq (a:=a) (b:=b) ==> @equality _) (fun f => etgt f).
Proof.
  unfold Proper, respectful, comma_morphism_eq.
  intros.
  destruct H.
  exact H0.
Qed.

Instance comma_morphism_eq_equiv {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} : Equivalence (comma_morphism_eq (a:=a) (b:=b)).
Proof.
  apply Build_Equivalence.
  - unfold Reflexive.
    intro.
    split. reflexivity. reflexivity.
  - unfold Symmetric.
    intros.
    split.
    + symmetry.
      apply (esrc_proper x).
      exact H.
    + symmetry.
      apply (etgt_proper x).
      exact H.
  - unfold Transitive.
    intros.
    destruct H, H0.
    constructor.
    + rewrite H, H0.
      reflexivity.
    + rewrite H1, H2.
      reflexivity.
Qed.

Lemma esrc_comp {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b c : comma_pair K L} (g : comma_morphism b c) (f : comma_morphism a b) : esrc (comma_comp g f) == esrc g ∘ esrc f.
Proof.
  unfold comma_comp, esrc.
  simpl.
  reflexivity.
Qed.

Lemma etgt_comp {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b c : comma_pair K L} (g : comma_morphism b c) (f : comma_morphism a b) : etgt (comma_comp g f) == etgt g ∘ etgt f.
Proof.
  unfold comma_comp, etgt.
  simpl.
  reflexivity.
Qed.

Lemma esrc_id {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a : comma_pair K L} : esrc (comma_id a) == identity.
Proof.
  unfold comma_id, esrc.
  simpl.
  reflexivity.
Qed.

Lemma etgt_id {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a : comma_pair K L} : etgt (comma_id a) == identity.
Proof.
  unfold comma_id, etgt.
  simpl.
  reflexivity.
Qed.

Program Definition Comma {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) : Category :=
  Build_Category_from_Type
    {|
      cat_object := comma_pair K L;
      cat_hom := comma_morphism;
      cat_hom_equal := fun _ _ => comma_morphism_eq;
      cat_identity := comma_id;
      cat_comp := comma_comp;
    |}.
Next Obligation.
  constructor.
  - rewrite esrc_comp.
    rewrite esrc_comp.
    rewrite (esrc_proper x y H).
    rewrite (esrc_proper x0 y0 H0).
    reflexivity.
  - rewrite etgt_comp.
    rewrite etgt_comp.
    rewrite (etgt_proper x y H).
    rewrite (etgt_proper x0 y0 H0).
    reflexivity.
Defined.
Next Obligation.
  constructor.
  - repeat rewrite esrc_comp.
    rewrite assoc_of.
    reflexivity.
  - repeat rewrite etgt_comp.
    rewrite assoc_of.
    reflexivity.
Defined.
Next Obligation.
  constructor.
  - rewrite esrc_comp.
    rewrite esrc_id.
    rewrite left_id_of.
    reflexivity.
  - rewrite etgt_comp.
    rewrite etgt_id.
    rewrite left_id_of.
    reflexivity.
Defined.
Next Obligation.
  constructor.
  - rewrite esrc_comp.
    rewrite esrc_id.
    rewrite right_id_of.
    reflexivity.
  - rewrite etgt_comp.
    rewrite etgt_id.
    rewrite right_id_of.
    reflexivity.
Defined.

Notation "K ↓ L" := (Comma K L) (at level 50).

Lemma esrc_preserve_extend {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b a' b'} {f : a ⟶ b in K ↓ L} (p : a = a') (q : b = b') : esrc (extend p q f) == extend (ltac: (rewrite p; reflexivity)) (ltac: (rewrite q; reflexivity)) (esrc f).
Proof.
  destruct p, q.
  rewrite extend_eq.
  rewrite extend_eq.
  reflexivity.
Qed.

Lemma etgt_preserve_extend {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b a' b'} {f : a ⟶ b in K ↓ L} (p : a = a') (q : b = b') : etgt (extend p q f) == extend (ltac: (rewrite p; reflexivity)) (ltac: (rewrite q; reflexivity)) (etgt f).
Proof.
  destruct p, q.
  rewrite extend_eq.
  rewrite extend_eq.
  reflexivity.
Qed.

Instance comma_map_proper {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : K ↓ L} {prf : forall f g, fmap L g ∘ cedge a == cedge b ∘ fmap K f} : Proper (@equality _ ==> @equality _ ==> comma_morphism_eq) (fun (f : csrc a ⟶ csrc b) g => [comma_map: f,g natural by prf f g]).
Proof.
  unfold Proper, respectful.
  intros.
  constructor.
  - simpl.
    exact H.
  - simpl.
    exact H0.
Qed.

Program Definition comma_π₁ {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) : Functor (K ↓ L) D₁ :=
  Build_Functor_from_Type
    {|
      funct_obj := fun (a : object (K ↓ L)) => csrc a;
      funct_map := fun _ _ f => esrc f;
    |}.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Definition comma_π₂ {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) : Functor (K ↓ L) D₂ :=
  Build_Functor_from_Type
    {|
      funct_obj := fun (a : object (K ↓ L)) => ctgt a;
      funct_map := fun _ _ f => etgt f;
    |}.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Definition comma_pairmap_π_morphism {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) {a b : K ↓ L} (f : a ⟶ b) := [comma_map: fmap (comma_π₁ K L) f, fmap (comma_π₂ K L) f].
Next Obligation.
  destruct f as [esrc etgt prop].
  rewrite prop.
  reflexivity.
Defined.

(*
Lemma comma_pairmap_π {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : K ↓ L} {f : a ⟶ b} :
  comma_pairmap_π_morphism f ≈ f in K ↓ L.
Proof.
  destruct f.
  unfold comma_pairmap_π_morphism.
  unfold comma_π₁, fmap; simpl.
  constructor.
  constructor.
  - reflexivity.
  - reflexivity.
Qed.
*)

Program Definition comma_nat {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C)
  : Nat (K ∘f comma_π₁ K L) (L ∘f comma_π₂ K L) := [Nat: fun a => cedge a].
Next Obligation.
  apply Build_Is_Nat.
  intros.

  refine
    (`begin
      fmap (L ∘f comma_π₂ K L) f ∘ cedge a
     =⟨ hom_refl ⟩
      (fmap L (fmap (comma_π₂ K L) f)) ∘ cedge a
     =⟨ hom_refl ⟩
      fmap L (etgt f) ∘ cedge a
     =⟨ is_comma_morphism f ⟩
      cedge b ∘ fmap K (esrc f)
     =⟨ hom_refl ⟩
      cedge b ∘ fmap (K ∘f comma_π₁ K L) f
      `end).
Defined.

Module CommaUniversality.
Section CommaUniversality.
  Context {C D₁ D₂ : Category}.
  Context (K : Functor D₁ C) (L : Functor D₂ C).
  
  Program Definition mediating (E : Category) (P : Functor E D₁) (P' : Functor E D₂) (η : Nat (K ∘f P) (L ∘f P')) : Functor E (K ↓ L) :=
    [fmap: fun _ _ f => [comma_map: fmap P f , fmap P' f] with fun e => [comma_pair: η e] : object (K ↓ L)].
  Next Obligation.
    apply (naturality_of η).
  Defined.
  Next Obligation.
    unfold Proper, respectful.
    intros.

    constructor.
    - unfold esrc.
      rewrite H.
      reflexivity.
    - unfold etgt.
      rewrite H.
      reflexivity.
  Defined.
  Next Obligation.
    constructor.
    - unfold esrc.
      simpl.
      apply fmap_identity.
    - unfold etgt.
      simpl.
      apply fmap_identity.
  Defined.
  Next Obligation.
    constructor.
    - unfold esrc.
      simpl.
      apply fmap_compose.
    - unfold etgt.
      simpl.
      apply fmap_compose.
  Defined.

  Lemma mediating_π₁ : forall {E P P'} η, comma_π₁ K L ∘f @mediating E P P' η ==f P.
  Proof.
    unfold eqFunctor.
    intros.
    exists (fun x => eq_refl).
    intros.
    rewrite extend_eq.
    reflexivity.
  Qed.
    
  Lemma mediating_π₂ : forall {E P P'} η, comma_π₂ K L ∘f @mediating E P P' η ==f P'.
  Proof.
    unfold eqFunctor.
    intros.
    exists (fun x => eq_refl).
    intros.
    rewrite extend_eq.
    reflexivity.
  Qed.

  Theorem universality :
    forall (E : Category) (P : Functor E D₁) (P' : Functor E D₂) (η : Nat (K ∘f P) (L ∘f P')),
      ∃! H from E to (K ↓ L) in Cat, ∃ (eq₁ : (comma_π₁ K L ∘f H) ==f P), ∃ (eq₂ : comma_π₂ K L ∘f H ==f P'),
      (L f⋆ nat_of_from_eqf eq₂) ∘n assocFunctor ∘n (comma_nat K L ⋆f H)
      == η ∘n (K f⋆ nat_of_from_eqf eq₁) ∘n assocFunctor in [E,C].
  Proof.
    intros.
    exists (@mediating E P P' η).
    constructor.

    - exists (mediating_π₁ η).
      exists (mediating_π₂ η).
      simpl.
      intro.
      unfold eq_to_hom.

      refine
        (`begin
          (fmap L ((extend eq_refl (⟨exist: mediating_π₂ η ⟩ A)) identity) ∘ identity) ∘ η A
         =⟨ _ ⟩
          fmap L identity ∘ η A
         =⟨ _ ⟩
          η A ∘ fmap K identity
         =⟨ _ ⟩
          η A ∘ fmap K (extend eq_refl (⟨exist: mediating_π₁ η ⟩ A) identity)
         ↑⟨ right_id_of ⟩
          (η A ∘ fmap K (extend eq_refl (⟨exist: mediating_π₁ η ⟩ A) identity)) ∘ identity
         `end).

      + rewrite fmap_preserve_extend.
        rewrite extend_eq.
        reflexivity.
      + rewrite fmap_identity.
        rewrite fmap_identity.
        rewrite left_id_of.
        rewrite right_id_of.
        reflexivity.
      + rewrite fmap_preserve_extend.
        rewrite extend_eq.
        rewrite right_id_of.
        reflexivity.

    - intros.
      simpl.
      unfold eqFunctor.

      assert (forall x, mediating η x = g x).
      { unfold mediating; intro.
        unfold fmap; simpl.
        apply comma_pair_equal.
        unfold eq_comma_pair.
        destruct H, H.
        destruct x0, x1.
        simpl in H.
        exists (conj (~ x0 x) (~ x1 x)).

        generalize (H x).
        unfold eq_to_hom.
        rewrite fmap_preserve_extend.
        rewrite fmap_identity.
        rewrite right_id_of.
        rewrite fmap_preserve_extend.
        rewrite fmap_identity.
        rewrite <- extend_compose_left.
        rewrite extend_eq.
        rewrite left_id_of.
        rewrite right_id_of.
        intro.

        assert (cedge (g x) == (extend eq_refl (fobj_eq (~ x1 x))) (η x ∘ (extend eq_refl (fobj_eq (x0 x))) identity)).
        { rewrite <- H0.
          rewrite extend_trans.
          rewrite extend_eq.
          reflexivity. }

        rewrite H1.
        rewrite extend_compose_factor.
        rewrite extend_eq.
        rewrite extend_compose_flip_l.
        rewrite extend_eq.
        rewrite right_id_of.
        rewrite extend_trans.
        rewrite extend_irrelevance.
        reflexivity.
      }

      exists H0.
      intros.
      destruct H, H.

      assert (fmap (mediating η) f == extend (~ H0 a) (~ H0 b) (fmap g f)).
      {
        split.
        - assert (esrc (fmap (mediating η) f) == fmap P f).
          reflexivity.

          rewrite H1.
          destruct x.
          simpl in H.
          rewrite <- (e a b f).
          rewrite esrc_preserve_extend.
          apply extend_irrelevance.
        - assert (etgt (fmap (mediating η) f) == fmap P' f).
          reflexivity.

          rewrite H1.
          destruct x0.
          simpl in H.
          rewrite <- (e a b f).
          rewrite etgt_preserve_extend.
          apply extend_irrelevance.
      }

      rewrite H1.
      rewrite extend_trans.
      rewrite extend_eq.
      reflexivity.
  Qed.
End CommaUniversality.
End CommaUniversality.
  
