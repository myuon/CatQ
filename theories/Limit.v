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
    ua_object : D;
    ua_map : c ⟶ G ua_object;
    ua_UMP : forall {d : D} {f : c ⟶ G d}, ∃! (g : ua_object ⟶ d) in D, fmap G g ∘ ua_map == f;
  }.
 
Program Definition Build_UniversalArrow_from_Type {C D : Category} (c : C) (G : Functor D C) (UA : UniversalArrow_Type c G) : UniversalArrow c G :=
  {|
    initial := [comma_pair: (ua_map UA) from F1 to (ua_object UA)];
  |}.
Next Obligation.
  destruct (ua_UMP UA (d:=ctgt x) (f:=cedge x)).
  destruct H.
  destruct x as [xs xt xe].

  unfold hom, morphism.
  simpl.
  refine (ex_intro _ [comma_map: F1, x0 from [comma_pair: (ua_map UA : Δ(c) _ ⟶ G _)] to [comma_pair: xe]] _).
  { constructor.
  - trivial.
  - intros.
    constructor.
    + simpl. trivial.
    + simpl.
      destruct g as [gs gt prop].
      simpl in prop.
      simpl.
      apply H0.
      rewrite prop.
      simpl.
      apply right_id_of. }

  Unshelve.
  simpl.
  simpl in H, H0.
  rewrite H.
  rewrite right_id_of.
  reflexivity.
Defined.

Program Definition Destruct_UniversalArrow_Type {C D : Category} (c : C) (G : Functor D C) (UA : UniversalArrow c G) : UniversalArrow_Type c G :=
  {|
    ua_object := ctgt (initial UA);
    ua_map := cedge (initial UA);
  |}.
Next Obligation.
  destruct (is_initial UA ([comma_pair: (f : Δ(c) F1 ⟶ _)])).
  exists (etgt x).
  constructor.
  - rewrite (is_comma_morphism x).
    simpl.
    rewrite right_id_of.
    reflexivity.
  - intros.
    destruct H.
    assert (fmap G g ∘ cedge (initial UA) == f ∘ fmap Δ(c) identity).
    + simpl.
      rewrite H0.
      rewrite right_id_of.
      reflexivity.
    + generalize (H1 [comma_map: (identity : csrc (initial UA) ⟶ csrc _), g from (initial UA) to [comma_pair: (f : Δ(c) F1 ⟶ _)] natural by H2] ltac:(trivial)).
      intro.
      rewrite H3.
      reflexivity.
Defined.

Definition Limit {C J : Category} (T : [ J , C ]) := UniversalArrow T (const_lift).

Definition is_complete (C : Category) :=
  forall {J} (F : Functor J C), Limit F.

Program Definition lim_Sets_is {J : Category} {T : Functor J Setoids} : Limit T :=
  Build_UniversalArrow_from_Type
    {|
      ua_object := (morphism (Δ SOne) T : Setoids);
    |}.
Admitted.

Theorem Setoids_complete : is_complete Setoids.
Admitted.

