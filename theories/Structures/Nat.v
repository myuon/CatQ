Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Setoids Category Functor Morphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

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

Notation "[Nat: comp 'as' F 'to' G 'by' prf ]" := (@Build_Nat _ _ F G comp prf).
Notation "[Nat: comp 'as' F 'to' G ]" := [Nat: comp as F to G by _].
Notation "[Nat: comp 'by' prf ]" := [Nat: comp as _ to _ by _].
Notation "[Nat: comp ]" := [Nat: comp by _].

Definition naturality_of {C D} {F G : Functor C D} (α : Nat F G) :
  forall {a b} {f : a ⟶ b},
    fmap G f ∘ α a == α b ∘ fmap F f
  := @naturality C D F G (component α) (is_nat α).

Definition natiso {C D} {F G : Functor C D} (α : Nat F G)
  := forall {a}, invertible (component α a).

Program Definition natiso_inv {C D} {F G : Functor C D} {α : Nat F G} : natiso α → Nat G F :=
  fun iso_α => [Nat: fun a => iso_α a ⁻¹].
Next Obligation.
  apply Build_Is_Nat.
  intros.
  destruct iso_α.
  destruct iso_α.
  simpl.

  assert (fmap F f == x0 ∘ fmap G f ∘ α a).

  refine
    (`begin
      fmap F f
     =⟨ ltac: (rewrite <- left_id_of; reflexivity) ⟩
      identity ∘ fmap F f
     =⟨ ltac: (rewrite <- (proj2 a1); reflexivity) ⟩
      (x0 ∘ α b) ∘ fmap F f
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      x0 ∘ (α b ∘ fmap F f)
     =⟨ ltac: (rewrite <- naturality_of; reflexivity) ⟩
      x0 ∘ (fmap G f ∘ α a)
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (x0 ∘ fmap G f) ∘ α a
      `end).

  refine
    (`begin
      fmap F f ∘ x
     =⟨ ltac: (rewrite H; reflexivity) ⟩
      ((x0 ∘ fmap G f) ∘ α a) ∘ x
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      (x0 ∘ fmap G f) ∘ (α a ∘ x)
     =⟨ ltac: (rewrite (proj1 a0); reflexivity) ⟩
      (x0 ∘ fmap G f) ∘ identity
     =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      x0 ∘ fmap G f
     `end).
Defined.

Program Definition idNat {C D : Category} (F : Functor C D) : Nat F F :=
  [Nat: fun a => @identity D (fobj F a)].
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
  [Nat: fun a => component β a ∘ component α a].
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

Notation "α ∘n β" := (compNat α β) (at level 40).

Program Definition compFNat {C D E : Category} (F : Functor D E) {G H : Functor C D} (α : Nat G H) : Nat (F ∘f G) (F ∘f H)
  := [Nat: fun a => fmap F (α a)].
Next Obligation.
  constructor.
  intros.
  refine
    (`begin
      fmap (F ∘f H) f ∘ fmap F (α a)
     =⟨ hom_refl ⟩
      fmap F (fmap H f) ∘ fmap F (α a)
     =⟨ ltac: (rewrite <- fmap_compose; reflexivity) ⟩
      fmap F (fmap H f ∘ α a)
     =⟨ ltac: (rewrite naturality_of; reflexivity) ⟩
      fmap F (α b ∘ fmap G f)
     =⟨ ltac: (rewrite fmap_compose; reflexivity) ⟩
      fmap F (α b) ∘ fmap F (fmap G f)
     =⟨ hom_refl ⟩
      fmap F (α b) ∘ fmap (F ∘f G) f
     `end).
Defined.

Notation "F f⋆ α" := (compFNat F α) (at level 40).
  
Program Definition compNatF {C D E : Category} {G H : Functor D E} (α : Nat G H) (F : Functor C D) : Nat (G ∘f F) (H ∘f F)
  := [Nat: fun a => α (F a)].
Next Obligation.
  constructor.
  intros.
  refine
    (`begin
      fmap (H ∘f F) f ∘ α (F a)
     =⟨ hom_refl ⟩
      fmap H (fmap F f) ∘ α (F a)
     =⟨ ltac: (rewrite naturality_of; reflexivity) ⟩
      α (F b) ∘ fmap G (fmap F f)
     =⟨ hom_refl ⟩
      α (F b)∘ fmap (G ∘f F) f
     `end).
Defined.

Notation "α ⋆f F" := (compNatF α F) (at level 40).

(* monoidal structure in 2-Cat *)
Program Definition assocFunctor {B C D E} {F : Functor B C} {G : Functor C D} {H : Functor D E} : Nat ((H ∘f G) ∘f F) (H ∘f (G ∘f F))
  := [Nat: fun a => @identity E (H (G (F a)))].
Next Obligation.
  constructor.
  intros.
  simpl.
  rewrite right_id_of.
  rewrite left_id_of.
  apply hom_refl.
Defined.

Program Definition assocInvFunctor {B C D E} {F : Functor B C} {G : Functor C D} {H : Functor D E} : Nat (H ∘f (G ∘f F)) ((H ∘f G) ∘f F)
  := [Nat: fun a => @identity E (H (G (F a)))].
Next Obligation.
  constructor.
  intros.
  simpl.
  rewrite right_id_of.
  rewrite left_id_of.
  apply hom_refl.
Defined.

Program Definition rightIdFunctor {C D} {F : Functor C D} : Nat (F ∘f idFunctor) F
  := [Nat: fun a => identity].
Next Obligation.
  constructor.
  intros.
  simpl.
  rewrite right_id_of.
  rewrite left_id_of.
  apply hom_refl.
Defined.

Program Definition leftIdFunctor {C D} {F : Functor C D} : Nat (idFunctor ∘f F) F
  := [Nat: fun a => identity].
Next Obligation.
  constructor.
  intros.
  simpl.
  rewrite right_id_of.
  rewrite left_id_of.
  apply hom_refl.
Defined.

Definition is_eq_nat {C D} {F G : Functor C D} (α : Nat F G)
  := forall {a}, an_arrow (α a) ≈ an_arrow (identity (x:=F a)).

Lemma Heq_hom_invertible {C} {f g : @arrow C} : f ≈ g → invertible (from_arrow f) → invertible (from_arrow g).
Proof.
  intros.
  unfold invertible in X.

  destruct (Heq_eq H) as [(f',g')].
  destruct y, H1, H2, H3.
  rewrite <- H1; simpl in H2,H3.
  simpl.

  rewrite <- H0 in X.
  simpl in X.

  destruct X.
  exists x.
  rewrite H4 in a.
  exact a.
Defined.

Lemma is_eqnat_natiso {C D} {F G : Functor C D} (α : Nat F G) : is_eq_nat α → natiso α.
Proof.
  intro.
  intro.
  generalize (H a).
  intro.
  generalize (Equivalence_Symmetric (Equivalence:=Heq_hom_equiv) [arr:α a] [arr:@identity _ (F a)] H0); intro.
  apply (Heq_hom_invertible H1).
  simpl.
  exists identity.
  rewrite right_id_of.
  split.
  reflexivity.
  reflexivity.
Qed.

Instance Heq_hom_equiv {C : Category} : Equivalence (fun f g => f ≈ g in C).
Definition eqFunctor_as_nat {C D} (F G : Functor C D) := { α : _ & @is_eq_nat _ _ F G α }.

Notation "F ==f G" := (eqFunctor_as_nat F G) (at level 40).

Program Definition eqn_fobj_iso {C D} {F G : Functor C D} {a} : F ==f G → F a ≃ G a in D
  := fun FG => [iso: projT1 FG a with natiso_inv (is_eqnat_natiso (projT2 FG)) a ].
Admit Obligations.

(*
Lemma eqn_fmap {C D} {F G : Functor C D} {a b} (f : a ⟶ b in C) : F ==f G → an_arrow (fmap F f) ≈ an_arrow (fmap G f).
Admitted.
 *)


