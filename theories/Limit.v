Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import Concrete Comma FunCat.
Require Import CatQ.Functors.Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Definition Is_UniversalArrow {C D : Category} (c : C) (G : Functor D C) := @Terminal (Δ(c) ↓ G).

Definition Limit {C J : Category} (T : [ J , C ]) := Is_UniversalArrow T (const_lift).

Definition is_complete (C : Category) :=
  forall {J} (F : Functor J C), Limit F.

