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
  destruct H.
  destruct x as [xs xt xe].

  unfold hom, morphism.
  simpl.
  refine (ex_intro _ [comma_map: tt, x0 from [comma_pair: (ua_map UA : Δ(c) _ ⟶ G _)] to [comma_pair: xe]] _).
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
    destruct H.
    assert (fmap G g ∘ cedge (initial UA) == f ∘ fmap Δ(c) identity).
    + simpl.
      rewrite H0.
      rewrite right_id_of.
      reflexivity.
    + generalize (H1 [comma_map: (identity : csrc (initial UA) ⟶ csrc _), g from (initial UA) to [comma_pair: (f : Δ(c) tt ⟶ _)] natural by H2] ltac:(trivial)).
      intro.
      rewrite H3.
      reflexivity.
Defined.

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
  destruct H.
  destruct x as [xs xt xe].

  unfold hom, morphism.
  simpl.
  refine (ex_intro _ [comma_map: x0, tt from [comma_pair: xe] to [comma_pair: (coua_map UA : G _ ⟶ Δ(c) _)]] _).
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

Definition Limit {C J : Category} (T : [ J , C ]) := CouniversalArrow T Δ.

Definition is_complete (C : Category) :=
  forall {J} (F : Functor J C), Limit F.

Program Definition lim_Sets_is {J : Category} {T : [J,Setoids]} : Limit T :=
  Build_CouniversalArrow_from_Type
    {|
      coua_object := (morphism (Δ SOne) T : Setoids);
      coua_map := {| component := fun j => {| mapping := fun α => α j tt |}; |} : Δ (@morphism [J,Setoids] (Δ SOne) T : Setoids) ⟶ T;
    |}.
Next Obligation.
  unfold Proper, respectful; simpl.
  intros.
  apply (H j tt).
Defined.
Next Obligation.
  constructor; simpl.
  intros.
  refine
    (`begin
      fmap T f (x a tt)
     =⟨ _ ⟩
      ((fmap T f) ∘ (x a)) tt
     =⟨ mapoid_apply (tt : SOne) (naturality_of x) ⟩
      ((x b) ∘ (fmap (Δ[J](SOne)) f)) tt
     =⟨ _ ⟩
      x b tt
      `end).
  reflexivity.
  reflexivity.
Defined.
Next Obligation.
  destruct f as [compf propf].
  simpl.
  simpl in compf.
  refine (ex_intro _ ({| mapping := fun d => {| component := fun j => {| mapping := fun k => compf j d |} : Δ SOne j ⟶ T j |} : Δ SOne ⟶ T |}) _).
  {
    constructor.
    - simpl.
      reflexivity.
    - simpl.
      intros.
      rewrite <- (H A x).
      destruct x0.
      reflexivity.
  }
  Unshelve.

  - unfold Proper, respectful; simpl.
    reflexivity.
  - constructor.
    simpl.
    intros.
    destruct propf.
    simpl in naturality.
    rewrite (naturality a b f d).
    reflexivity.
  - simpl.
    unfold Proper, respectful; simpl.
    intros.
    rewrite H.
    reflexivity.
Defined.

Theorem Setoids_complete : is_complete Setoids.
Proof.
  unfold is_complete.
  intros.
  exact (lim_Sets_is (T:=F)).
Defined.  


