Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat Comma.
From CatQ.Functors Require Import Concrete.
Require Import CatQ.UniversalArrow CatQ.Limit.
Require Import CatQ.Kan.KanExt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(*
Program Definition Lan_of_eq {C D U} {F F' : Functor C D} {E : Functor C U} : F ==f F' → (F†E) ⇋ (F'†E) :=
  fun eqF =>
    pair (fun lan => [lan: lan_functor lan with (lan_functor lan f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n lan_unit lan])
         (fun lan' => [lan: lan_functor lan' with (lan_functor lan' f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n lan_unit lan']).
Next Obligation.
  assert (F' ==f F).
  { symmetry; assumption. }

  exists (proj1_sig (is_lan lan ((S f⋆ proj1_sig (eqf_to_eqn H)) ∘n θ))).
  constructor.
  - intro.
    refine
      (`begin
        θ A
       =⟨ _ ⟩
        ((S f⋆ (proj1_sig (eqf_to_eqn eqF) ∘n proj1_sig (eqf_to_eqn H))) ∘n θ) A
       =⟨ _ ⟩
        (((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n (S f⋆ proj1_sig (eqf_to_eqn H))) ∘n θ) A
       =⟨ assoc_of ⟩
        ((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n ((S f⋆ proj1_sig (eqf_to_eqn H)) ∘n θ)) A
       =⟨ _ ⟩
        ((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n ((⟨lan: (S f⋆ proj1_sig (eqf_to_eqn H)) ∘n θ of lan⟩ ⋆f F) ∘n lan_unit lan)) A
       ↑⟨ assoc_of ⟩
        (((S f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n (⟨lan: (S f⋆ proj1_sig (eqf_to_eqn H)) ∘n θ of lan⟩ ⋆f F)) ∘n lan_unit lan) A
       =⟨ _ ⟩
        (((⟨lan: (S f⋆ ⟨exist: eqf_to_eqn H ⟩) ∘n θ ⟩ ⋆f F') ∘n (lan_functor lan f⋆ proj1_sig (eqf_to_eqn eqF))) ∘n lan_unit lan) A
       =⟨ assoc_of ⟩
        ((⟨lan: (S f⋆ ⟨exist: eqf_to_eqn H ⟩) ∘n θ ⟩ ⋆f F') ∘n ((lan_functor lan f⋆ proj1_sig (eqf_to_eqn eqF)) ∘n lan_unit lan)) A
       `end).
    + simpl.
    is_lan :
      forall (S : Functor D U) (θ : Nat E (S ∘f F)),
        ∃! (τ : Nat lan_functor S) in [D,U], θ == (τ ⋆f F) ∘n lan_unit in [C,U];
 *)

(*
Section pointwise.
  Context {C D U : Category}.
  Context {F : Functor C D} {E : Functor C U}.
  Context {has_kan : forall d, comma_π₂ F Δ(d) † (E ∘f comma_π₁ F Δ(d))}.

  Definition has_colim : forall d, Colimit (E ∘f comma_π₁ F Δ(d))
    := fun d => fst colim_as_Lan_along_One (has_kan d).

  Program Definition Lan_obj : object D → object U :=
    fun a => colim_object (has_colim a).

  Section map_part.
    Context {d d' : D} {h : d ⟶ d'}.

    Definition comma_nat_d' : Nat (F ∘f comma_π₁ F Δ(d)) (Δ(d') ∘f comma_π₂ F Δ(d)) := (Δ(h as d to d') ⋆f comma_π₂ F Δ(d)) ∘n comma_nat F Δ(d).
    
    Definition mediating_functor : Functor (F ↓ Δ(d)) (F ↓ Δ(d')) :=
      ⟨exist: CommaUniversality.universality (E:= F ↓ Δ(d)) comma_nat_d'⟩.

    Lemma mediating_f_prop :
      ∃ (eq₁ : (comma_π₁ F Δ(d') ∘f mediating_functor) ==f comma_π₁ F Δ(d)), ∃ (eq₂ : comma_π₂ F Δ(d') ∘f mediating_functor ==f comma_π₂ F Δ(d)),
          (Δ(d') f⋆ nat_of_from_eqf eq₂) ∘n assocFunctor ∘n (comma_nat F Δ(d') ⋆f mediating_functor)
          == comma_nat_d' ∘n (F f⋆ nat_of_from_eqf eq₁) ∘n assocFunctor in [F ↓ Δ(d), D].
    Proof.
      exact (proj1 (proj2_sig (CommaUniversality.universality (E:= F ↓ Δ(d)) comma_nat_d'))).
    Qed.

    (*
    Definition mu_d_nat : Nat (E ∘f comma_π₁ F Δ(d)) (Δ(Lan_obj d) ∘f comma_π₂ F Δ(d))
      := lan_unit (snd colim_as_Lan_along_One (has_colim d)).
    
    Program Definition Lan_map_h : Lan_obj d ⟶ Lan_obj d' :=
      ⟨exist: is_lan has_kan_π₂ _⟩.
*)

  End map_part.

End pointwise.
*)
