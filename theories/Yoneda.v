Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Structures.
Require Import CatQ.Categories.FunCat.
Require Import CatQ.Functors.Bifunctor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition yoneda {C : Category} : Functor C (PSh[C]) :=
  [fmap: fun _ _ f => homFunctor[-,f]n with fun a => (homFunctor[-,a] : PSh[C]) ].
Next Obligation.
  unfold Proper, respectful.
  intros.
  unfold Bifunctor_apply_R.
  simpl.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  rewrite right_id_of.
  rewrite left_id_of.
  reflexivity.
Defined.
Next Obligation.
  rewrite right_id_of.
  rewrite right_id_of.
  rewrite right_id_of.
  apply assoc_of.
Defined.

Program Definition YonedaLemma_right {C : Category} {a : C} {F : PSh[C]} : @morphism PSh[C] (yoneda a) F -⇒ F a
  := [mapoid: fun yaF => yaF a identity].
Next Obligation.
  solve_proper.
Defined.

Program Definition YonedaLemma_left {C : Category} {a : C} {F : PSh[C]} : F a -⇒ @morphism (PSh[C]) (yoneda a) F
  := [mapoid: fun Fa => [Nat: fun (b : opposite C) => [mapoid: fun (ba : opposite_obj b ⟶ a) => fmap F ba Fa] ] ].
Next Obligation.
  unfold Proper, respectful.
  intros.
  apply mapoid_apply.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  constructor.
  simpl.
  intros.

  refine
    (`begin
      (fmap F f) (fmap F x Fa)
     =⟨ _ ⟩
      (fmap F f ∘ fmap F x) Fa
     =⟨ _ ⟩
      fmap F (f ∘{opposite C} (x ∘{opposite C} identity)) Fa
     =⟨ _ ⟩
      fmap F ((identity ∘ x) ∘ f) Fa
     `end).
  - reflexivity.
  - apply mapoid_apply.
    rewrite <- fmap_compose.
    rewrite right_id_of.
    reflexivity.
  - reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful.
  simpl.
  intros.
  rewrite H.
  reflexivity.
Defined.

Lemma Yoneda {C : Category} {a : C} {F : PSh[C]} : @morphism (PSh[C]) (yoneda a) F ≃ F a in Setoids.
Proof.
  refine [iso: (YonedaLemma_right : @hom Setoids _ _) with (YonedaLemma_left : @hom Setoids _ _) ].
  constructor.
  - unfold YonedaLemma_right, YonedaLemma_left.
    simpl.
    intros.

    refine
      (`begin
        fmap F x0 ((x a) identity)
       =⟨ ltac: (apply Setoids_comp_apply; reflexivity) ⟩
        (fmap F x0 ∘ x a) identity
       =⟨ mapoid_apply identity (naturality_of x) ⟩
        (x A ∘ fmap (homFunctor[-,a]) x0) identity
       =⟨ ltac: (apply Setoids_comp_apply; reflexivity) ⟩
        (x A) (fmap (homFunctor[-,a]) x0 identity)
       =⟨ mapoid_cong (x A) hom_refl ⟩
        (x A) ((identity ∘ identity) ∘ x0)
       =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
        (x A) (identity ∘ x0)
       =⟨ ltac: (rewrite left_id_of; reflexivity) ⟩
        (x A) x0
       `end).
    
  - unfold YonedaLemma_right, YonedaLemma_left.
    simpl.
    intros.
    
    refine
      (`begin
        (fmap F identity) x
       =⟨ mapoid_apply x (fmap_identity F) ⟩
        @identity Setoids _ x
       =⟨ _ ⟩
        x
       `end).

    reflexivity.
Qed.

Program Definition yF {C : Category} {F : PSh[C]} : Functor (opposite C) Setoids :=
  [fmap: fun a b f => [mapoid: fun yaF => yaF ∘ fmap yoneda (opposite_hom f)]
   with fun a => (morphism (yoneda (opposite_obj a)) F : object Setoids)].
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  unfold opposite_obj, opposite_hom.
  unfold Proper, respectful.
  simpl.
  intros.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  unfold opposite_hom.
  rewrite left_id_of.
  rewrite right_id_of.
  reflexivity.
Defined.
Next Obligation.
  apply mapoid_cong.
  rewrite right_id_of.
  rewrite right_id_of.
  rewrite right_id_of.
  simpl.
  rewrite <- assoc_of.
  reflexivity.
Defined.

Program Definition yoneda_lemma_nat {C : Category} {F : PSh[C]} : Nat yF F :=
  [Nat: fun a => @YonedaLemma_right C a F].
Next Obligation.
  constructor.
  unfold YonedaLemma_right.
  simpl.
  intros.

  refine
    (`begin
      fmap F f (x a identity)
     =⟨ ltac: (apply Setoids_comp_apply) ⟩
      (fmap F f ∘ x a) identity
     =⟨ ltac: (apply mapoid_apply; apply naturality_of) ⟩
      (x b ∘ fmap (homFunctor[-,opposite_obj a]) f) identity
     =⟨ ltac: (apply Setoids_comp_apply) ⟩
      (x b) (fmap (homFunctor[-,opposite_obj a]) f identity)
     =⟨ mapoid_cong (x b) hom_refl ⟩
      x b ((identity ∘{C} identity) ∘{C} opposite_hom f)
     =⟨ ltac: (rewrite left_id_of; rewrite left_id_of; reflexivity) ⟩ 
      x b (opposite_hom f)
     ↑⟨ ltac: (rewrite right_id_of; rewrite right_id_of; reflexivity) ⟩
      x b ((opposite_hom f ∘{C} identity) ∘{C} identity)
      `end).
Defined.

Theorem yoneda_ff {C : Category} : ff (@yoneda C).
Proof.
  unfold ff.
  intros.

  generalize (@Yoneda C a (yoneda b)).
  intro.
  destruct X as [X1 X2 Xprop].

  refine [iso: X2 with X1].
  destruct Xprop.
  constructor.
  - apply iso_on_right.
  - apply iso_on_left.
Qed.

(*
Corollary yoneda_ff_on_hom {C : Category} {a b : C} : (natiso : yoneda a x -≃→ yoneda b x) → isomorphic a b  
*)  

