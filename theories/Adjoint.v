Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure Adjoint {C D} (F : Functor C D) (G : Functor D C) :=
  {
    adjunction : forall {c d}, morphism (F c) d ≃ morphism c (G d) at Setoids;
    adj_natural_L :
      forall {c c' d} (f : c ⟶ c'),
        ([mapoid: fun k => k ∘ f by ltac: (solve_proper)] : morphism c' (G d) ⟶ morphism c (G d) in Setoids) ∘ iso_right (@adjunction c' d) == iso_right (@adjunction c d) ∘ ([mapoid: fun k => k ∘ fmap F f by ltac: (solve_proper)]);
    adj_natural_R :
      forall {c d d'} (g : d ⟶ d'),
        ([mapoid: fun k => fmap G g ∘ k by ltac: (solve_proper)] : morphism c (G d) ⟶ morphism c (G d') in Setoids) ∘ iso_right (@adjunction c d) == iso_right (@adjunction c d') ∘ ([mapoid: fun k => g ∘ k by ltac: (solve_proper)]);
  }.


