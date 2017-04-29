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

Definition Limit {C J : Category} (T : [ J , C ]) := CouniversalArrow T Δ.

Notation "[limit: L , π 'of' T ]" := (Build_CouniversalArrow_from_Type (c:=T) {| coua_object := L; coua_map := π; |}).
Notation "[limit: L , π ]" := [limit: L , π of _].

Definition of_lim_obj {C J T} (lim: @Limit C J T) : C := coua_object (Destruct_CouniversalArrow_Type lim).
Definition of_lim_map {C J T} (lim: @Limit C J T) : Δ[J](of_lim_obj lim) ⟶ T in [J,C] := coua_map (Destruct_CouniversalArrow_Type lim).

Definition is_complete (C : Category) :=
  forall {J} (F : Functor J C), Limit F.

Definition Colimit {C J : Category} (T : [ J , C ]) := UniversalArrow T Δ.

Notation "[colimit: L , π 'of' T ]" := (Build_UniversalArrow_from_Type (c:=T) {| ua_object := L; ua_map := π; |}).
Notation "[colimit: L , π ]" := [colimit: L , π of _].

Definition of_colim_obj {C J T} (colim: @Colimit C J T) : C := ua_object (Destruct_UniversalArrow_Type colim).
Definition of_colim_map {C J T} (colim: @Colimit C J T) : T ⟶ Δ[J](of_colim_obj colim) in [J,C] := ua_map (Destruct_UniversalArrow_Type colim).

Definition is_cocomplete (C : Category) :=
  forall {J} (F : Functor J C), Colimit F.

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
       equalizer (limit_from_spr_eq_Eql spr eql F) ,
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
       ↑⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
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




