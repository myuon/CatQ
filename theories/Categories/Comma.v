Require Import Morphisms Setoid Coq.Program.Equality.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
Require Import CatQ.Categories.FunCat.
Require Import CatQ.Yoneda.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Definition comma_pair {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C)
  := @sigT (object D₁ * object D₂) (fun d => hom (K (fst d)) (L (snd d))).

Definition csrc {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (p : comma_pair K L) : object D₁
  := fst (projT1 p).
Definition ctgt {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (p : comma_pair K L) : object D₂
  := snd (projT1 p).
Definition cedge {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (p : comma_pair K L) : hom (K (csrc p)) (L (ctgt p))
  := projT2 p.

Definition comma_morphism {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (a b : comma_pair K L)
  := { h : hom (csrc a) (csrc b) * hom (ctgt a) (ctgt b)
     | fmap L (snd h) ∘ (cedge a) == (cedge b) ∘ fmap K (fst h) }.

Definition esrc {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} (p : comma_morphism a b) : hom (csrc a) (csrc b)
  := fst (proj1_sig p).
Definition etgt {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} (p : comma_morphism a b) : hom (ctgt a) (ctgt b)
  := snd (proj1_sig p).

Program Definition comma_id {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (a : comma_pair K L) : comma_morphism a a
  := @exist _ _ (@identity D₁ _, @identity D₂ _) _.
Next Obligation.
  rewrite fmap_identity.
  rewrite fmap_identity.
  rewrite right_id_of.
  rewrite left_id_of.
  reflexivity.
Defined.

Program Definition comma_comp {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} (a b c : comma_pair K L) (g : comma_morphism b c) (f : comma_morphism a b) : comma_morphism a c
  := @exist _ _ (esrc g ∘ esrc f, etgt g ∘ etgt f) _.
Next Obligation.
  exact
    (`begin
      fmap L (etgt g ∘ etgt f) ∘ cedge a
     =⟨ ltac: (rewrite fmap_compose; reflexivity) ⟩
      fmap L (etgt g) ∘ fmap L (etgt f) ∘ cedge a
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      fmap L (etgt g) ∘ (fmap L (etgt f) ∘ cedge a)
     =⟨ ltac: (rewrite (proj2_sig f); reflexivity) ⟩
      fmap L (etgt g) ∘ (cedge b ∘ fmap K (esrc f))
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (fmap L (etgt g) ∘ cedge b) ∘ fmap K (esrc f)
     =⟨ ltac: (rewrite (proj2_sig g); reflexivity) ⟩
      (cedge c ∘ fmap K (esrc g)) ∘ fmap K (esrc f)
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      cedge c ∘ (fmap K (esrc g) ∘ fmap K (esrc f))
     =⟨ ltac: (rewrite <- fmap_compose; reflexivity) ⟩
      cedge c ∘ fmap K (esrc g ∘ esrc f)
     `end).
Defined.

Program Definition comma_pair_eq {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) (f g : comma_pair K L) : Prop.
refine (exists (src_eq: csrc f = csrc g), exists (tgt_eq: ctgt f = ctgt g), _).
refine (cedge f == _).
rewrite src_eq, tgt_eq.
exact (cedge g).
Defined.

Definition comma_morphism_eq {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} (f g : comma_morphism a b)
  := esrc f == esrc g /\ etgt f == etgt g.

Instance esrc_proper {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} (p : comma_morphism a b) : Proper (comma_morphism_eq (a:=a) (b:=b) ==> @equality _) esrc.
Proof.
  unfold Proper, respectful, comma_morphism_eq.
  intros.
  destruct H.
  exact H.
Qed.

Instance etgt_proper {C D₁ D₂} {K : Functor D₁ C} {L : Functor D₂ C} {a b : comma_pair K L} (p : comma_morphism a b) : Proper (comma_morphism_eq (a:=a) (b:=b) ==> @equality _) etgt.
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
    rewrite (esrc_proper x x y H).
    rewrite (esrc_proper x0 x0 y0 H0).
    reflexivity.
  - rewrite etgt_comp.
    rewrite etgt_comp.
    rewrite (etgt_proper x x y H).
    rewrite (etgt_proper x0 x0 y0 H0).
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

Program Definition comma_π₁ {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) : Functor (K ↓ L) D₁ :=
  Build_Functor_from_Type
    {|
      funct_obj := fun (a : object (K ↓ L)) => csrc a;
      funct_map := fun _ _ f => esrc f;
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  destruct H.
  exact H.
Defined.
Next Obligation.
  rewrite esrc_id.
  reflexivity.
Defined.
Next Obligation.
  unfold esrc.
  simpl.
  unfold esrc.
  reflexivity.
Defined.

Program Definition comma_π₂ {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) : Functor (K ↓ L) D₂ :=
  Build_Functor_from_Type
    {|
      funct_obj := fun (a : object (K ↓ L)) => ctgt a;
      funct_map := fun _ _ f => etgt f;
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  destruct H.
  exact H0.
Defined.
Next Obligation.
  rewrite etgt_id.
  reflexivity.
Defined.
Next Obligation.
  unfold etgt.
  simpl.
  unfold etgt.
  reflexivity.
Defined.

Program Definition comma_nat {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) : Nat (K ∘f comma_π₁ K L) (L ∘f comma_π₂ K L) :=
  {|
    component := fun a => cedge a;
  |}.
Next Obligation.
  apply Build_Is_Nat.
  intros.

  refine
    (`begin
      fmap (L ∘f comma_π₂ K L) f ∘ cedge a
     =⟨ _ ⟩
      (fmap L (fmap (comma_π₂ K L) f)) ∘ cedge a
     =⟨ _ ⟩
      fmap L (etgt f) ∘ cedge a
     =⟨ proj2_sig f ⟩
      cedge b ∘ fmap K (esrc f)
     =⟨ _ ⟩
      cedge b ∘ fmap (K ∘f comma_π₁ K L) f
      `end).

  reflexivity.
  reflexivity.
  reflexivity.
Defined.

Program Definition comma_nat_universal_map {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) (E : Category) (P : Functor E D₁) (P' : Functor E D₂) (η : Nat (K ∘f P) (L ∘f P')) : Functor E (K ↓ L) :=
  Build_Functor_from_Type
    {|
      funct_obj := fun e => (@existT _ _ (P e , P' e) (η e) : object (K ↓ L));
      funct_map := fun _ _ f => @exist _ _ (fmap P f , fmap P' f) _;
    |}.
Next Obligation.
  apply (naturality_of η).
Defined.
Next Obligation.
  unfold csrc, ctgt.
  simpl.
  unfold Proper, respectful.
  intros.

  constructor.
  - unfold esrc.
    simpl.
    rewrite H.
    reflexivity.
  - unfold etgt.
    simpl.
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
    unfold esrc.
    simpl.
    apply fmap_compose.
  - unfold etgt.
    simpl.
    unfold etgt.
    simpl.
    apply fmap_compose.
Defined.

(*
setoid上の∃!を定義する.
eqFunctorの定義も見直す？

Theorem comma_nat_universality {C D₁ D₂} (K : Functor D₁ C) (L : Functor D₂ C) :
  forall (E : Category) (P : Functor E D₁) (P' : Functor E D₂) (η : Nat (K ∘f P) (L ∘f P')),
    exists ! (H : Functor E (K ↓ L)), eqFunctor (comma_π₁ K L ∘f H) P /\ eqFunctor (comma_π₂ K L ∘f H) P'.
Proof.
  intros.

  exists (comma_nat_universal_map η).
  constructor.

  - split.
    + unfold eqFunctor.
      assert (fobj (comma_π₁ K L ∘f comma_nat_universal_map η) = fobj P).
      * reflexivity.
      * exists H.
        unfold eqFmap.
        intros.

        refine
          (`begin
            fmap (comma_π₁ K L ∘f comma_nat_universal_map η) f
           =⟨ _ ⟩
            fmap (comma_π₁ K L) (fmap (comma_nat_universal_map η) f)
           =⟨ _ ⟩
            fmap P f
           =⟨ _ ⟩
            eq_rect_r (fun t => morphism (t a) (t b)) (fmap P f) H
           `end).

        reflexivity.
        reflexivity.

        unfold eq_rect_r.
        simpl_eqs.
        reflexivity.
    + assert (fobj (comma_π₂ K L ∘f comma_nat_universal_map η) = fobj P').
      * reflexivity.
      * exists H.
        unfold eqFmap.
        intros.

        refine
          (`begin
            fmap (comma_π₂ K L ∘f comma_nat_universal_map η) f
           =⟨ _ ⟩
            fmap (comma_π₂ K L) (fmap (comma_nat_universal_map η) f)
           =⟨ _ ⟩
            fmap P' f
           =⟨ _ ⟩
            eq_rect_r (fun t => morphism (t a) (t b)) (fmap P' f) H
           `end).

        reflexivity.
        reflexivity.

        unfold eq_rect_r.
        simpl_eqs.
        reflexivity.
  - intros.
    destruct H.
*)    
  

