Require Import Morphisms Setoid ProofIrrelevance.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Setoids Category Functor Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Section Heq.
  Inductive Heq_hom {C : Category} {a b : C} (f : hom a b) : forall {c d}, hom c d → Prop :=
  | mk_Heq_hom : forall {g : hom a b}, f == g → Heq_hom f g.

  Program Definition extend {C : Category} {a b c d : C} (ac: a = c) (bd: b = d) : morphism a b -⇒ morphism c d
    := [mapoid: fun f => eq_rect a (λ k, k ⟶ d in C) (eq_rect b (λ k, a ⟶ k in C) f d bd) c ac].
  Next Obligation.
    solve_proper.
  Defined.

  Lemma extend_refl {C : Category} {a b : C} {f : a ⟶ b} : extend eq_refl eq_refl f = f.
  Proof.
    unfold extend.
    simpl.
    reflexivity.
  Qed.

  Axiom Heq_eq : forall {C : Category} {a b c d : C} (f : hom a b) (g : hom c d),
      Heq_hom f g → { eq : a = c /\ b = d | extend (proj1 eq) (proj2 eq) f == g }.
End Heq.

Notation "f ≈ g 'in' C" := (@Heq_hom C _ _ f _ _ g) (at level 70, g at next level).
Infix "≈" := Heq_hom (at level 70, only parsing).

Section Heq_Lemmas.
  Lemma Heq_eq_same_hom {C : Category} {a b : C} (f : hom a b) (g : hom a b) : f ≈ g → f == g.
  Proof.
    intros.
    destruct (Heq_eq H).
    destruct x.
    rewrite <- e.

    assert (e0 = eq_refl).
    { apply proof_irrelevance. }
    assert (e1 = eq_refl).
    { apply proof_irrelevance. }

    rewrite H0.
    rewrite H1.

    assert (proj1 (conj (eq_refl : a = a) (eq_refl : b = b)) = eq_refl).
    { apply proof_irrelevance. }
    assert (proj2 (conj (eq_refl : a = a) (eq_refl : b = b)) = eq_refl).
    { apply proof_irrelevance. }

    rewrite H2, H3.
    rewrite extend_refl.
    reflexivity.
  Qed.

  Lemma Heq_trans_hetero {C : Category} {a1 b1 a2 b2 a3 b3 : C} {f : a1 ⟶ b1} {g : a2 ⟶ b2} {h : a3 ⟶ b3} : f ≈ g → g ≈ h → f ≈ h.
  Proof.
    intros.
    destruct H.
    destruct H0.
    constructor.
    rewrite H.
    exact H0.
  Qed.

  Lemma Heq_sym_hetero {C : Category} {a1 b1 a2 b2 : C} {f : a1 ⟶ b1} {g : a2 ⟶ b2} : f ≈ g → g ≈ f.
  Proof.
    intros.
    destruct H.
    constructor.
    symmetry.
    exact H.
  Qed.

  Lemma Heq_hom_equiv {C : Category} {a b : C} : Equivalence (fun f g => @Heq_hom C a b f a b g).
  Proof.
    constructor.
    - unfold Reflexive.
      intros.
      constructor.
      reflexivity.
    - unfold Symmetric.
      intros.
      destruct H.
      symmetry in H.
      constructor.
      exact H.
    - unfold Transitive.
      intros.
      destruct H.
      destruct H0.
      constructor.
      rewrite H, H0.
      reflexivity.
  Qed.
End Heq_Lemmas.

Section Hom_From_Eq.
  Definition hom_from_eq {C : Category} {a b : C} (ab: a = b) : {f : a ⟶ b | f ≈ @identity _ b}.
    rewrite ab.
    exists identity.
    constructor.
    reflexivity.
  Defined.

  Lemma hom_from_eq_refl {C : Category} {a : C} : proj1_sig (@hom_from_eq C a a eq_refl) = identity.
  Proof.
    unfold hom_from_eq.
    simpl.
    reflexivity.
  Qed.

  Definition hom_from_heqdom {C : Category} {a b c d : C} {f : a ⟶ b} {g : c ⟶ d} :
    f ≈ g → a ⟶ c.
  Proof.
    intro.
    destruct (Heq_eq H).
    destruct x.
    rewrite e0.
    exact identity.
  Defined.

  Lemma hom_from_heqdom_left {C : Category} {a' a b c d : C} {f : a ⟶ b} {g : c ⟶ d} {h : a' ⟶ a} (fg : f ≈ g)
    : hom_from_heqdom fg ∘ h ≈ h.
  Proof.
    destruct fg.
    unfold hom_from_heqdom.
    destruct (Heq_eq (mk_Heq_hom e)).
    destruct x.
    constructor.

    assert (e1 = eq_refl).
    apply proof_irrelevance.

    rewrite H.
    unfold eq_rect_r.
    simpl.
    apply left_id_of.
  Qed.

  Lemma hom_from_heqdom_right {C : Category} {a b c c' d : C} {f : a ⟶ b} {g : c ⟶ d} {h : c ⟶ c'} (fg : f ≈ g)
    : h ∘ hom_from_heqdom fg ≈ h.
  Proof.
    destruct fg.
    unfold hom_from_heqdom.
    destruct (Heq_eq (mk_Heq_hom e)).
    destruct x.
    constructor.

    assert (e1 = eq_refl).
    apply proof_irrelevance.

    rewrite H.
    unfold eq_rect_r.
    simpl.
    apply right_id_of.
  Qed.
End Hom_From_Eq.

Section EqFunctor.
  Definition eqFunctor {C D} (F G : Functor C D) :=
    ∀ {a b} (f : a ⟶ b), fmap F f ≈ fmap G f.

  Lemma eqFunctor_obj {C D} {F F' : Functor C D} : eqFunctor F F' → forall a, F a = F' a.
  Proof.
    intros.
    destruct (H a a identity).
    reflexivity.
  Qed.
End EqFunctor.

Instance eqFunctor_equiv {C D} : Equivalence (@eqFunctor C D).
Proof.
  constructor.
  - unfold Reflexive.
    intro.
    constructor.
    reflexivity.
  - unfold Symmetric.
    intros.
    unfold eqFunctor.
    intros.
    unfold eqFunctor in H.
    destruct (H a b f).
    constructor.
    symmetry.
    exact H0.
  - unfold Transitive.
    intros.
    unfold eqFunctor.
    intros.
    destruct (H0 a b f).
    destruct (H a b f).
    constructor.
    rewrite H2, H1.
    reflexivity.
Defined.

Notation "F ==f G" := (eqFunctor F G) (at level 40).

Section Nat_Eqf.
  Definition nat_eqf {C D} (F G : Functor C D) :=
    {η : Nat F G | forall {a}, η a ≈ @identity _ (F a)}.
End Nat_Eqf.

Notation "F ==n G" := (nat_eqf F G) (at level 40).

Section Eqf_And_EqfNat.
  Program Definition nat_of_from_eqf {C D} (F G : Functor C D) : F ==f G → Nat F G
    := fun FG => [Nat: fun a => hom_from_heqdom (FG a a identity)].
  Next Obligation.
    constructor.
    intros.
    apply Heq_eq_same_hom.
    generalize (hom_from_heqdom_left (h:=fmap F f) (FG b b identity)); intro.
    generalize (hom_from_heqdom_right (h:=fmap G f) (FG a a identity)); intro.
    apply Heq_sym_hetero.
    apply (Heq_trans_hetero H).
    apply Heq_sym_hetero.
    apply (Heq_trans_hetero H0).
    apply Heq_sym_hetero.
    exact (FG a b f).
  Defined.
End Eqf_And_EqfNat.

