Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import Concrete Comma FunCat.
Require Import CatQ.Functors.Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Definition UniversalArrow {C D : Category} (c : C) (G : Functor D C) := @Initial (Δ(c) ↓ G).

Structure UniversalArrow_Type {C D : Category} (c : C) (G : Functor D C) :=
  {
    ua_object : object D;
    ua_map : c ⟶ G ua_object;
    ua_UMP : forall {d : object D} {f : c ⟶ G d}, ∃! (g : ua_object ⟶ d), fmap G g ∘ ua_map = f;
  }.

Program Definition Build_UniversalArrow_from_Type {C D : Category} (c : C) (G : Functor D C) (UA : UniversalArrow_Type c G) : UniversalArrow c G :=
  {|
    initial := [comma_pair: (ua_map UA) from F1 to (ua_object UA)];
  |}.
Next Obligation.
  destruct (ua_UMP UA (d:=ctgt x) (f:=cedge x)).
  destruct H.
  destruct x.

  unfold hom, morphism.
  simpl.
  refine (ex_intro _ [comma_map: F1, x0 from [comma_pair: (ua_map UA : Δ(c) _ ⟶ G _)] to [comma_pair: cedge]] _).
  constructor.
  - trivial.
  - intros.
    unfold equality.
    constructor.
    + simpl. trivial.
    + simpl.
      destruct g.
      simpl.
      apply H0.
      simpl.
      simpl in is_comma_morphism.
Admitted.

Definition Limit {C J : Category} (T : [ J , C ]) := UniversalArrow T (const_lift).

Definition is_complete (C : Category) :=
  forall {J} (F : Functor J C), Limit F.

Program Definition lim_Sets_is {J : Category} {T : Functor J Setoids} : Limit T :=
  {|
    initial := [comma_pair: _ from (F1 : One) to morphism (Δ SOne) T];
  |}.
Admit Obligations.

Theorem Setoids_complete : is_complete Setoids.
Admitted.

