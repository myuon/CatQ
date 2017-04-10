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

Definition Limit {C J : Category} (T : [ J , C ]) := CouniversalArrow T Δ.

Notation "[limit: L , π 'of' T ]" := (Build_CouniversalArrow_from_Type (c:=T) {| coua_object := L; coua_map := π; |}).
Notation "[limit: L , π ]" := [limit: L , π of _].

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
  refine (exist _ ({| mapping := fun d => {| component := fun j => {| mapping := fun k => compf j d |} : Δ SOne j ⟶ T j |} : Δ SOne ⟶ T |}) _).
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

Ltac assume := fun f term => generalize term; intro f.

Definition limit_from_spr_eq_Eql 
        {C : Category} (spr : has_sproduct C) (eql : has_equalizer C) :=
  fun J (F : [J,C]) =>
    let PFob := spr J F in
    let PFarr := spr arrow (fun arr => F (codarr arr)) in
    let s := ⟨sproduct: (fun arr => sproduct_proj PFob (codarr arr)) of PFarr⟩ in
    let t := ⟨sproduct: (fun arr => fmap F (from_arrow arr) ∘ sproduct_proj PFob (domarr arr)) of PFarr⟩ in
    let Eql := eql (sproduct PFob) (sproduct PFarr) s t in Eql.

Program Definition limit_from_spr_eq
        {C : Category} (spr : has_sproduct C) (eql : has_equalizer C) : is_complete C :=
  fun J (F : [J,C]) =>
    [limit:
       equalizer (limit_from_spr_eq_Eql spr eql F) ,
       [Nat: fun j => sproduct_proj (spr J F) j ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F)] : Δ[J](_) ⟶ F in [J,C] of F].
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap F f ∘ (sproduct_proj (spr J F) a ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F))
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (fmap F f ∘ sproduct_proj (spr J F) a) ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F)
     =⟨ _ ⟩
      (sproduct_proj (spr arrow (fun arr => F (codarr arr))) (an_arrow f) ∘ ⟨sproduct: (fun arr => fmap F (from_arrow arr) ∘ sproduct_proj (spr J F) (domarr arr)) of _⟩) ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F)
     =⟨ _ ⟩
      sproduct_proj (spr arrow (fun arr => F (codarr arr))) (an_arrow f) ∘ (⟨sproduct: (fun arr => fmap F (from_arrow arr) ∘ sproduct_proj (spr J F) (domarr arr)) of _⟩ ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F))
     =⟨ _ ⟩
      sproduct_proj (spr arrow (fun arr => F (codarr arr))) (an_arrow f) ∘ (⟨sproduct: (fun arr => sproduct_proj (spr J F) (codarr arr)) of _⟩ ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F))
     =⟨ _ ⟩
      (sproduct_proj (spr arrow (fun arr => F (codarr arr))) (an_arrow f) ∘ ⟨sproduct: (fun arr => sproduct_proj (spr J F) (codarr arr)) of _⟩) ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F)
     =⟨ _ ⟩
      (sproduct_proj (spr J F) b ∘ equalizing_map _) ∘ fmap (Δ[J](_)) f
     `end).

  - rewrite (@sproduct_mediating_prop _ arrow _ (spr arrow (fun arr => F (codarr arr))) _ (fun arr => fmap F (from_arrow arr) ∘ sproduct_proj (spr J F) (domarr arr)) (an_arrow f)).
    reflexivity.
  - rewrite assoc_of.
    reflexivity.
  - generalize ((is_equalizer (limit_from_spr_eq_Eql spr eql F))).
    intro.
    destruct X as [Xeq].
    rewrite Xeq.
    reflexivity.
  - rewrite assoc_of.
    reflexivity.
  - rewrite (@sproduct_mediating_prop _ arrow _ (spr arrow (fun arr => F (codarr arr))) _ (fun arr => sproduct_proj (spr J F) (codarr arr)) (an_arrow f)).
    rewrite right_id_of.
    reflexivity.
Defined.
Next Obligation.
  assert (⟨sproduct: fun i => (f i : d ⟶ F i) of spr J F⟩ [equalize] (⟨sproduct: fun arr => sproduct_proj (spr J F) (codarr arr) of _⟩, ⟨sproduct: fun arr => fmap F (from_arrow arr) ∘ sproduct_proj _ (domarr arr) of spr arrow (fun arr => F (codarr arr))⟩)).
  {
    apply (sproduct_pointwise_equal).
    intro.
    rewrite <- assoc_of.
    rewrite (sproduct_mediating_prop (spr arrow (fun arr => F (codarr arr)))).
    rewrite <- assoc_of.
    rewrite (sproduct_mediating_prop (spr arrow (fun arr => F (codarr arr)))).

    rewrite (sproduct_mediating_prop (spr J F)).
    rewrite assoc_of.
    rewrite (sproduct_mediating_prop (spr J F)).
    destruct i.
    simpl.

    refine
      (`begin
        f b
       =⟨ ltac: (rewrite <- right_id_of; reflexivity) ⟩
        f b ∘ fmap (Δ[J](d)) f0
       =⟨ ltac: (rewrite <- naturality_of; reflexivity) ⟩
        fmap F f0 ∘ f a
       `end).
  }

  refine (exist _ ⟨equalizer: ⟨sproduct: fun i => (f i : d ⟶ F i) of spr J F⟩ equalize by H of limit_from_spr_eq_Eql spr eql F⟩ _).
  constructor.
  - intro.
    rewrite assoc_of.
    rewrite (equalizer_mediating_prop (limit_from_spr_eq_Eql spr eql F)).
    rewrite (sproduct_mediating_prop (spr J F)).
    reflexivity.
  - intros.
    rewrite (equalizer_mediating_unique (p:=limit_from_spr_eq_Eql spr eql F) (k:=equalizing_map (limit_from_spr_eq_Eql spr eql F) ∘ g)).
    + apply equalizer_pointwise_equal.
      rewrite (equalizer_mediating_prop).
      assume ieql (is_equalizer (limit_from_spr_eq_Eql spr eql F)).
      destruct ieql.
      rewrite <- assoc_of.
      rewrite equalize_parallel.
      apply assoc_of.

      assume ieql (is_equalizer (limit_from_spr_eq_Eql spr eql F)).
      destruct ieql.
      rewrite <- assoc_of.
      rewrite equalize_parallel.
      apply assoc_of.

      rewrite equalizer_mediating_prop.
      reflexivity.
    + rewrite equalizer_mediating_prop.
      apply (sproduct_pointwise_equal).
      intro.
      rewrite sproduct_mediating_prop.
      symmetry.
      rewrite <- assoc_of.
      exact (H0 i).
      Unshelve.

  assume ieql (is_equalizer (limit_from_spr_eq_Eql spr eql F)).
  destruct ieql.
  rewrite <- assoc_of.
  rewrite equalize_parallel.
  apply assoc_of.
Defined.
  
Theorem sproduct_equalizer_imp_complete {C} : has_sproduct C → has_equalizer C → is_complete C.
Proof.
  exact (fun spr eql => limit_from_spr_eq spr eql).
Defined.




