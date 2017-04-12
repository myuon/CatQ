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
    initial := [comma_pair: (ua_map UA) from tt to (ua_object UA)];
  |}.
Next Obligation.
  destruct (ua_UMP UA (d:=ctgt x) (f:=cedge x)).
  destruct u.
  destruct x as [xs xt xe].

  unfold hom, morphism.
  simpl.
  refine (exist _ [comma_map: tt, x0 from [comma_pair: (ua_map UA : Δ(c) _ ⟶ G _)] to [comma_pair: xe]] _).
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
  destruct (is_initial UA ([comma_pair: (f : Δ(c) tt ⟶ _)])).
  exists (etgt x).
  constructor.
  - rewrite (is_comma_morphism x).
    simpl.
    rewrite right_id_of.
    reflexivity.
  - intros.
    destruct u.
    assert (fmap G g ∘ cedge (initial UA) == f ∘ fmap Δ(c) identity).
    + simpl.
      rewrite H.
      rewrite right_id_of.
      reflexivity.
    + generalize (H1 [comma_map: (identity : csrc (initial UA) ⟶ csrc _), g from (initial UA) to [comma_pair: (f : Δ(c) tt ⟶ _)] natural by H2] ltac:(trivial)).
      intro.
      rewrite H3.
      reflexivity.
Defined.

Notation "[universal: d 'with' f 'of' c , G ]" := (@Build_UniversalArrow_from_Type _ _ c G (@Build_UniversalArrow_Type _ _ c G d f _)).
Notation "[universal: d 'with' f ]" := [universal: d with f of _ , _].

Definition CouniversalArrow {C D : Category} (c : C) (G : Functor D C) := @Terminal (G ↓ Δ(c)).

Structure CouniversalArrow_Type {C D : Category} (c : C) (G : Functor D C) :=
  {
    coua_object : D;
    coua_map : G coua_object ⟶ c;
    coua_UMP : forall {d : D} {f : G d ⟶ c}, ∃! (g : d ⟶ coua_object) in D, coua_map ∘ fmap G g == f;
  }.

Program Definition Build_CouniversalArrow_from_Type {C D : Category} (c : C) (G : Functor D C) (UA : CouniversalArrow_Type c G) : CouniversalArrow c G :=
  {|
    terminal := [comma_pair: (coua_map UA) from (coua_object UA) to tt];
  |}.
Next Obligation.
  destruct (coua_UMP UA (d:=csrc x) (f:=cedge x)).
  destruct u.
  destruct x as [xs xt xe].

  unfold hom, morphism.
  simpl.
  refine (exist _ [comma_map: x0, tt from [comma_pair: xe] to [comma_pair: (coua_map UA : G _ ⟶ Δ(c) _)]] _).
  { constructor.
  - trivial.
  - intros.
    constructor.
    + simpl.
      destruct g as [gs gt prop].
      simpl in prop.
      simpl.
      apply H0.
      rewrite <- prop.
      simpl.
      apply left_id_of.
    + simpl.
      trivial. }

  Unshelve.
  simpl.
  simpl in H, H0.
  rewrite H.
  rewrite left_id_of.
  reflexivity.
Defined.
