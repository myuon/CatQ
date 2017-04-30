Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat Comma Concrete.
From CatQ.Functors Require Import Concrete.
Require Import CatQ.UniversalArrow CatQ.Limit CatQ.Equality.
Require Import CatQ.Kan.KanExt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition Lan_of_eq {C D U} {F F' : Functor C D} {E : Functor C U} : F ==f F' → (F†E) → (F'†E) :=
  fun eqF =>
    (fun lan => [lan: lan_functor lan with (lan_functor lan f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n lan_unit lan]).
Next Obligation.
  exists (proj1_sig (is_lan lan ((S f⋆ proj1_sig (eqf_to_eqn (symmetry eqF))) ∘n θ))).
  constructor.
  - intro.
    refine
      (`begin
        θ A
       =⟨ _ ⟩
        ((S f⋆ (proj1_sig (eqf_to_eqn eqF) ∘n proj1_sig (eqf_to_eqn (symmetry eqF)))) ∘n θ) A
       =⟨ _ ⟩
        (((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n (S f⋆ proj1_sig (eqf_to_eqn (symmetry eqF)))) ∘n θ) A
       =⟨ assoc_of ⟩
        ((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n ((S f⋆ proj1_sig (eqf_to_eqn (symmetry eqF))) ∘n θ)) A
       =⟨ _ ⟩
        ((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n ((⟨lan: (S f⋆ proj1_sig (eqf_to_eqn (symmetry eqF))) ∘n θ of lan⟩ ⋆f F) ∘n lan_unit lan)) A
       ↑⟨ assoc_of ⟩
        (((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n (⟨lan: (S f⋆ proj1_sig (eqf_to_eqn (symmetry eqF))) ∘n θ of lan⟩ ⋆f F)) ∘n lan_unit lan) A
       =⟨ _ ⟩
        (((⟨lan: (S f⋆ ⟨exist: eqf_to_eqn (symmetry eqF) ⟩) ∘n θ ⟩ ⋆f F') ∘n (lan_functor lan f⋆ proj1_sig (eqf_to_eqn eqF))) ∘n lan_unit lan) A
       =⟨ assoc_of ⟩
        ((⟨lan: (S f⋆ ⟨exist: eqf_to_eqn (symmetry eqF) ⟩) ∘n θ ⟩ ⋆f F') ∘n ((lan_functor lan f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n lan_unit lan)) A
       `end).

    + simpl.
      unfold eq_to_hom.
      rewrite fmap_preserve_extend, fmap_identity.
      rewrite fmap_preserve_extend, fmap_identity.
      rewrite <- extend_compose_left.
      rewrite extend_eq.
      rewrite left_id_of.
      rewrite extend_id_flip_l.
      rewrite <- extend_compose_right, extend_eq.
      rewrite right_id_of.
      destruct (⟨exist: eqF⟩).
      reflexivity.
    + generalize (lan_mediating_prop_at lan (θ := (S f⋆ ⟨exist: eqf_to_eqn (symmetry eqF) ⟩) ∘n θ) (A:=A)).
      simpl.
      intro.
      rewrite <- H.
      reflexivity.
    + generalize (fstar_distr (S:=S) (α := ⟨exist: eqf_to_eqn eqF⟩) (β := ⟨exist: eqf_to_eqn (symmetry eqF)⟩)).
      simpl.
      intro.
      rewrite (H A).
      reflexivity.
    + generalize (eqn_sym_inv_r eqF).
      simpl.
      intro.
      rewrite (H A).
      rewrite fmap_identity, left_id_of.
      reflexivity.

  - intros.
    symmetry.
    apply lan_mediating_unique.
    intro; simpl.
    rewrite (H A).
    unfold eq_to_hom.
    rewrite fmap_preserve_extend, fmap_identity.
    rewrite fmap_preserve_extend, fmap_identity.
    rewrite <- extend_compose_left.
    rewrite extend_eq, left_id_of.
    rewrite <- extend_compose_left.
    rewrite extend_eq, left_id_of.
    rewrite extend_compose_flip_l.
    rewrite extend_eq.
    rewrite extend_compose_left.
    rewrite fobj_eq_preserve_sym.
    rewrite (eq_sym_of_eqf eqF).
    rewrite nat_extend.
    reflexivity.
Defined.

Section pointwise.
  Context {C D U : Category}.
  Context {F : Functor C D} {E : Functor C U}.
  Context {has_colim : forall d, Colimit (E ∘f comma_π₁ F Δ(d))}.

  Definition has_kan : forall d, comma_π₂ F Δ(d) † (E ∘f comma_π₁ F Δ(d))
    := fun d => Lan_of_eq (symmetry functor_to_One_unique) (snd colim_as_Lan_along_One (has_colim d)).

  Program Definition Lan_obj : object D → object U :=
    fun a => colim_object (has_colim a).

  Section map_part.
    Context {d d' : D} (h : d ⟶ d').

    Definition comma_nat_d' : Nat (F ∘f comma_π₁ F Δ(d)) (Δ(d') ∘f comma_π₂ F Δ(d)) := (Δ(h as d to d') ⋆f comma_π₂ F Δ(d)) ∘n comma_nat F Δ(d).
    
    Definition mediating_functor : Functor (F ↓ Δ(d)) (F ↓ Δ(d')) :=
      ⟨exist: CommaUniversality.universality (E:= F ↓ Δ(d)) comma_nat_d'⟩.

    Lemma mediating_f_prop :
      ∃ (eq₁ : (comma_π₁ F Δ(d') ∘f mediating_functor) ==f comma_π₁ F Δ(d)),
      ∃ (eq₂ : comma_π₂ F Δ(d') ∘f mediating_functor ==f comma_π₂ F Δ(d)),
          (Δ(d') f⋆ nat_of_from_eqf eq₂) ∘n assocFunctor ∘n (comma_nat F Δ(d') ⋆f mediating_functor)
          == comma_nat_d' ∘n (F f⋆ nat_of_from_eqf eq₁) ∘n assocFunctor in [F ↓ Δ(d), D].
    Proof.
      exact (proj1 (proj2_sig (CommaUniversality.universality (E:= F ↓ Δ(d)) comma_nat_d'))).
    Qed.

    Definition eq_H_r: (comma_π₁ F Δ(d') ∘f mediating_functor) ==f comma_π₁ F Δ(d).
    Proof.
      destruct mediating_f_prop.
      exact x.
    Qed.
    Definition eq_H_l: (comma_π₂ F Δ(d') ∘f mediating_functor) ==f comma_π₂ F Δ(d).
    Proof.
      destruct mediating_f_prop.
      destruct H.
      exact x0.
    Qed.

    Definition mu_d'_nat : Nat (E ∘f comma_π₁ F Δ(d)) (lan_functor (has_kan d') ∘f comma_π₂ F Δ(d))
      := (lan_functor (has_kan d') f⋆ proj1_sig (eqf_to_eqn eq_H_l)) ∘n assocFunctor ∘n (lan_unit (has_kan d') ⋆f mediating_functor) ∘n assocInvFunctor ∘n (E f⋆ proj1_sig (eqf_to_eqn (symmetry eq_H_r))).
  End map_part.

  Definition Lan_map_h {d d'} (h : d ⟶ d') : lan_functor (has_kan d) ⟶ lan_functor (has_kan d') in [One,U] :=
    ⟨lan: lan_functor (has_kan d') with mu_d'_nat h of has_kan d ⟩.

  (*
  Program Definition pLan : F † E
    := [lan: [fmap: fun a b h => (Lan_map_h h) tt with fun a => lan_functor (has_kan a) tt ] ].
  Admitted.
   *)

End pointwise.
