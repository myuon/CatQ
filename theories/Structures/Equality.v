Require Import Morphisms Setoid ProofIrrelevance.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Setoids Category Functor Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Section Heq_Lemmas.
  Lemma Heq_eq_same_hom {C : Category} {a b : C} (f : hom a b) (g : hom a b) : heq_extending f g → f == g in C.
  Proof.
    intros.
    destruct (heq_extending_eq H).
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

  Lemma Heq_trans_hetero {C : Category} {a1 b1 a2 b2 a3 b3 : C} {f : a1 ⟶ b1} {g : a2 ⟶ b2} {h : a3 ⟶ b3} : heq_extending f g → heq_extending g h → heq_extending f h.
  Proof.
    intros.
    destruct H.
    destruct H0.
    constructor.
    rewrite H.
    exact H0.
  Qed.

  Lemma Heq_sym_hetero {C : Category} {a1 b1 a2 b2 : C} {f : a1 ⟶ b1} {g : a2 ⟶ b2} : heq_extending f g → heq_extending g f.
  Proof.
    intros.
    destruct H.
    constructor.
    symmetry.
    exact H.
  Qed.
End Heq_Lemmas.

(*
Section Hom_From_Eq.
  Definition hom_from_eq {C : Category} {a b : C} (ab: a = b) : {f : a ⟶ b | heq_extending f (@identity _ b)}.
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
    f ≈ g in C → a ⟶ c.
  Proof.
    intro.
    destruct (heq_extending_eq H).
    destruct x.
    rewrite e0.
    exact identity.
  Defined.

  Lemma hom_from_heqdom_left {C : Category} {a' a b c d : C} {f : a ⟶ b} {g : c ⟶ d} {h : a' ⟶ a} (fg : heq_extending f g)
    : heq_extending (hom_from_heqdom fg ∘ h) h.
  Proof.
    destruct fg.
    unfold hom_from_heqdom.
    destruct (heq_extending_eq (mk_heq_extending e)).
    destruct x.
    constructor.

    assert (e1 = eq_refl).
    apply proof_irrelevance.

    rewrite H.
    unfold eq_rect_r.
    simpl.
    apply left_id_of.
  Qed.

  Lemma hom_from_heqdom_right {C : Category} {a b c c' d : C} {f : a ⟶ b} {g : c ⟶ d} {h : c ⟶ c'} (fg : heq_extending f g)
    : heq_extending (h ∘ hom_from_heqdom fg) h.
  Proof.
    destruct fg.
    unfold hom_from_heqdom.
    destruct (heq_extending_eq (mk_heq_extending e)).
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
 *)

Section EqFunctor.
  Definition eqFunctor {C D} (F G : Functor C D) :=
    ∀ {a b} (f : a ⟶ b), fmap F f ≈ fmap G f in D.
End EqFunctor.

Instance eqFunctor_equiv {C D} : Equivalence (@eqFunctor C D).
Proof.
  constructor.
  - unfold Reflexive.
    intro.
    unfold eqFunctor.
    intros.
    apply hrefl.
  - unfold Symmetric.
    intros.
    unfold eqFunctor.
    intros.
    apply hsym.
    apply H.
  - unfold Transitive.
    intros.
    unfold eqFunctor.
    intros.
    apply (htrans (H a b f) (H0 a b f)).
Defined.

Notation "F ==f G" := (eqFunctor F G) (at level 40).

Section Nat_Eqf.
  Definition nat_eqf {C D} (F G : Functor C D) :=
    {η : Nat F G | forall {a}, heq_extending (η a) (@identity _ (F a))}.
End Nat_Eqf.

Notation "F ==n G" := (nat_eqf F G) (at level 40).

(*
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
 *)

