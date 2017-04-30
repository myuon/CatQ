Require Import Morphisms Setoid ProofIrrelevance.
Require Import Utf8.

Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import Concrete Comma FunCat.
Require Import CatQ.Functors.Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure UniversalArrow {C D : Category} (c : C) (G : Functor D C) :=
  {
    ua_object : D;
    ua_map : c ⟶ G ua_object;
    is_ua : forall {d : D} {f : c ⟶ G d}, ∃! (g : ua_object ⟶ d) in D, fmap G g ∘ ua_map == f;
  }.
  
Notation "[universal: d 'with' f 'of' c , G 'by' prf ]" := (@Build_UniversalArrow _ _ c G d f prf).
Notation "[universal: d 'with' f 'of' c , G ]" := [universal: d with f of c , G by _].
Notation "[universal: d 'with' f ]" := [universal: d with f of _ , _].

Section Section_IComma_UA.
  Definition IComma_UA {C D : Category} (c : C) (G : Functor D C) := @Initial (Δ(c) ↓ G).

  Program Definition UA_as_IComma {C D : Category} (c : C) (G : Functor D C) :
    UniversalArrow c G ⇋ IComma_UA c G
    := pair (fun UA => [initial: [comma_pair: (ua_map UA : Δ(c) tt ⟶ G _) as (tt : One) to (ua_object UA)] ])
            (fun IC => [universal: ctgt (initial IC) with cedge (initial IC)]).
  Next Obligation.
    destruct (is_ua UA (d:=ctgt x) (f:=cedge x)).
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
  Next Obligation.
    destruct (is_initial IC ([comma_pair: (f : Δ(c) tt ⟶ _)])).
    exists (etgt x).
    constructor.
    - rewrite (is_comma_morphism x).
      simpl.
      rewrite right_id_of.
      reflexivity.
    - intros.
      destruct u.
      assert (fmap G g ∘ cedge (initial IC) == f ∘ fmap Δ(c) identity).
      + simpl.
        rewrite H.
        rewrite right_id_of.
        reflexivity.
      + generalize (H1 [comma_map: (identity : csrc (initial IC) ⟶ csrc _), g from (initial IC) to [comma_pair: (f : Δ(c) tt ⟶ _)] natural by H2] ltac:(trivial)).
        intro.
        rewrite H3.
        reflexivity.
  Defined.
  
End Section_IComma_UA.
  
Structure CoUniversalArrow {C D : Category} (c : C) (G : Functor D C) :=
  {
    coua_object : D;
    coua_map : G coua_object ⟶ c;
    is_coua : forall {d : D} {f : G d ⟶ c}, ∃! (g : d ⟶ coua_object) in D, coua_map ∘ fmap G g == f;
  }.

Notation "[couniversal: d 'with' f 'of' c , G ]" := (@Build_CoUniversalArrow _ _ c G d f _).
Notation "[couniversal: d 'with' f ]" := [couniversal: d with f of _ , _].

Section Section_TComma_CoUA.
  Definition TComma_CoUA {C D : Category} (c : C) (G : Functor D C) := @Terminal (G ↓ Δ(c)).

  Program Definition CoUA_as_TComma {C D : Category} (c : C) (G : Functor D C) :
    CoUniversalArrow c G ⇋ TComma_CoUA c G
    := pair (fun UA => [terminal: [comma_pair: (coua_map UA : _ ⟶ Δ(c) tt) as (coua_object UA) to (tt : One)] ])
            (fun TC => [couniversal: csrc (terminal TC) with cedge (terminal TC)]).
  Next Obligation.
    destruct (is_coua UA (d:=csrc x) (f:=cedge x)).
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
  Next Obligation.
    destruct (is_terminal TC ([comma_pair: (f : _ ⟶ Δ(c) tt)])).
    exists (esrc x).
    constructor.
    - rewrite <- (is_comma_morphism x).
      simpl.
      rewrite left_id_of.
      reflexivity.
    - intros.
      destruct u.
      assert (fmap Δ( c) (identity : ctgt (terminal TC) ⟶ ctgt (terminal TC)) ∘ cedge [comma_pair:f : G d ⟶ Δ( c) tt in C] == cedge (terminal TC) ∘{ C} fmap G g).
      + simpl.
        rewrite H.
        rewrite left_id_of.
        reflexivity.
      + generalize (H1 [comma_map: g,(identity : ctgt (terminal TC) ⟶ ctgt _) from [comma_pair: (f : _ ⟶ Δ(c) tt)] to (terminal TC) natural by H2] ltac:(trivial)).
        intro.
        rewrite H3.
        reflexivity.
  Defined.

End Section_TComma_CoUA.


