Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import Comma.
From CatQ.Functors Require Import Concrete.
Require Import CatQ.UniversalArrow CatQ.Limit.
Require Import CatQ.Kan.KanExt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(*
Section pointwise.
  Context {C D U : Category}.
  Context {F : Functor C D} {E : Functor C U}.
  Context {has_colim : forall d, Colimit (E ∘f comma_π₁ F (Δ(d)))}.

  Program Definition pFunctor : Functor D U :=
    [fmap: _ with fun a => ua_object (Destruct_UniversalArrow_Type (has_colim a)) ].

End pointwise.

Program Definition pLan : [lan:  ]
*)

