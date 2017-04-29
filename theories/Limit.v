Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import Concrete Comma FunCat.
Require Import CatQ.Functors.Concrete.
Require Import CatQ.UniversalArrow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Definition Cone {J C} (vertex : object C) (T : Functor J C) := Nat Δ[J](vertex) T.

Structure Limit {J C : Category} (T : Functor J C) :=
  {
    lim_object : C;
    lim_cone : Cone lim_object T;
    is_limit : forall {v} (cone : Cone v T), ∃! (h : v ⟶ lim_object) in C, lim_cone ∘n Δ(h as _ to _) == cone in [J,C];
  }.

Notation "[limit: L 'with' π 'of' T ]" := (@Build_Limit _ _ T L π _).
Notation "[limit: L 'with' π ]" := [limit: L with π of _].

Section Section_Limit_By_CoUA.
  Definition CoUA_Limit {J C : Category} (T : [J,C]) := CoUniversalArrow T Δ.

  Program Definition Limit_as_CoUA {J C} (T : Functor J C): Limit T ≃ CoUA_Limit T in Types
    := [iso: fun lim => [couniversal: lim_object lim with (lim_cone lim : @hom [J,C] _ _) ]
        with fun UA => [limit: coua_object UA with coua_map UA ] ].
  Next Obligation.
    apply (is_limit lim f).
  Defined.
  Next Obligation.
    apply (is_coua UA).
  Defined.
  Next Obligation.
    constructor.
    - intro; destruct x; auto.
    - intro; destruct x; auto.
  Defined.
End Section_Limit_By_CoUA.

Definition is_complete (C : Category) := forall {J} (F : Functor J C), Limit F.

Definition Cocone {J C} (vertex : object C) (T : Functor J C) := Nat T Δ[J](vertex).

Structure Colimit {J C : Category} (T : Functor J C) :=
  {
    colim_object : C;
    colim_cone : Cocone colim_object T;
    is_colimit : forall {v} (cocone : Cocone v T), ∃! (h : colim_object ⟶ v) in C, Δ(h as _ to _) ∘n colim_cone == cocone in [J,C];
  }.

Notation "[colimit: L 'with' π 'of' T ]" := (@Build_Colimit _ _ T L π _).
Notation "[colimit: L 'with' π ]" := [colimit: L with π of _].

Section Section_Colimit_By_UA.
  Definition UA_Colimit {J C : Category} (T : [J,C]) := UniversalArrow T Δ.

  Program Definition Colimit_as_UA {J C} (T : Functor J C): Colimit T ≃ UA_Colimit T in Types
    := [iso: fun colim => [universal: colim_object colim with (colim_cone colim : @hom [J,C] _ _)]
        with fun UA => [colimit: ua_object UA with ua_map UA] ].
  Next Obligation.
    apply (is_colimit colim f).
  Defined.
  Next Obligation.
    apply (is_ua UA).
  Defined.
  Next Obligation.
    constructor.
    - intro; destruct x; auto.
    - intro; destruct x; auto.
  Defined.
End Section_Colimit_By_UA.

Definition is_cocomplete (C : Category) := forall {J} (F : Functor J C), Colimit F.

Program Definition lim_Sets_is {J : Category} {T : [J,Setoids]} : Limit T :=
  {|
    lim_object := (morphism (Δ SOne) T : Setoids);
    lim_cone := [Nat: fun j => [mapoid: fun α => α j tt] ] : Δ (@morphism [J,Setoids] (Δ SOne) T : Setoids) ⟶ T;
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
     =⟨ Setoids_comp _ ⟩
      ((fmap T f) ∘ (x a)) tt
     =⟨ mapoid_apply (tt : SOne) (naturality_of x) ⟩
      ((x b) ∘ (fmap (Δ[J](SOne)) f)) tt
     =⟨ Setoids_comp _ ⟩
      x b tt
      `end).
Defined.
Next Obligation.
  destruct cone as [compf propf].
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

Inductive arrow {C : Category} : Type :=
| an_arrow: forall {a b : C} (f : a ⟶ b), arrow.

Notation "[arr: f ]" := (an_arrow f).

Definition domarr {C : Category} : @arrow C → C :=
  fun arr =>
    match arr with
      | (@an_arrow _ a _ _) => a
    end.

Definition codarr {C : Category} : @arrow C → C :=
  fun arr =>
    match arr with
      | (@an_arrow _ _ b _) => b
    end.

Definition from_arrow {C} (f : @arrow C) : domarr f ⟶ codarr f :=
  match f with
    | (@an_arrow _ _ _ f) => f
  end.

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
       equalizer (limit_from_spr_eq_Eql spr eql F) with
       [Nat: fun j => sproduct_proj (spr J F) j ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F)] : Δ[J](_) ⟶ F in [J,C] of F].
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap F f ∘ (sproduct_proj (spr J F) a ∘ equalizing_map (limit_from_spr_eq_Eql spr eql F))
     =⟨ _ ⟩
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

  - rewrite (@sproduct_mediating_prop _ arrow _ (spr arrow (fun arr => F (codarr arr))) _ (fun arr => sproduct_proj (spr J F) (codarr arr)) (an_arrow f)).
    rewrite right_id_of.
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
  - rewrite (@sproduct_mediating_prop _ arrow _ (spr arrow (fun arr => F (codarr arr))) _ (fun arr => fmap F (from_arrow arr) ∘ sproduct_proj (spr J F) (domarr arr)) (an_arrow f)).
    reflexivity.
  - rewrite assoc_of.
    reflexivity.
Defined.
Next Obligation.
  assert (⟨sproduct: fun i => (cone i : v ⟶ F i) of spr J F⟩ [equalize] (⟨sproduct: fun arr => sproduct_proj (spr J F) (codarr arr) of _⟩, ⟨sproduct: fun arr => fmap F (from_arrow arr) ∘ sproduct_proj _ (domarr arr) of spr arrow (fun arr => F (codarr arr))⟩)).
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
        cone b
       ↑⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
        cone b ∘ fmap (Δ[J](v)) f
       =⟨ ltac: (rewrite <- naturality_of; reflexivity) ⟩
        fmap F f ∘ cone a
       `end).
  }

  refine (exist _ ⟨equalizer: ⟨sproduct: fun i => (cone i : v ⟶ F i) of spr J F⟩ equalize by H of limit_from_spr_eq_Eql spr eql F⟩ _).
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
      generalize (is_equalizer (limit_from_spr_eq_Eql spr eql F)); intro ieql.
      destruct ieql.
      rewrite <- assoc_of.
      rewrite equalize_parallel.
      apply assoc_of.

      generalize (is_equalizer (limit_from_spr_eq_Eql spr eql F)); intro ieql.
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

  generalize (is_equalizer (limit_from_spr_eq_Eql spr eql F)); intro ieql.
  destruct ieql.
  rewrite <- assoc_of.
  rewrite equalize_parallel.
  apply assoc_of.
Defined.
  
Theorem sproduct_equalizer_imp_complete {C} : has_sproduct C → has_equalizer C → is_complete C.
Proof.
  exact (fun spr eql => limit_from_spr_eq spr eql).
Defined.




