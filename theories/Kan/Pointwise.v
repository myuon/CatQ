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

Section pointwise.
  Context {C D U : Category}.
  Context {F : Functor C D} {E : Functor C U}.
  Context {has_colim : forall d, Colimit (E ∘f comma_π₁ F (Δ(d)))}.

  Program Definition Lan_obj : object D → object U :=
    fun a => ua_object (Destruct_UniversalArrow_Type (has_colim a)).

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

    Program Definition has_kan_π₂ : Lan (comma_π₂ F Δ(d)) (E ∘f comma_π₁ F Δ(d)) :=
      [lan: [fmap: fun a b f => of_colim_map (has_colim b) with fun d => of_colim_obj (has_colim d)]].
    
    Program Definition Lan_map_h : Lan_obj d ⟶ Lan_obj d' :=
      ⟨exist: is_lan kan (S:=S) θ⟩.

  End map_part.

  Program Definition pFunctor : Functor D U :=
    [fmap: _ with fun a => ua_object (Destruct_UniversalArrow_Type (has_colim a)) ].

End pointwise.

