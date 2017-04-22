Require Import Morphisms ProofIrrelevance.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition Cat : Category :=
  Build_Category_from_Type
    {|
      cat_object := Category;
      cat_hom := Functor;
      cat_hom_equal := fun _ _ F G => (F ==f G : Prop);
      cat_hsetoid := HSetoid_on_setoid (fun X Y => [setoid: Functor X Y with fun F G => (F ==f G : Prop)]);
      cat_identity := @idFunctor;
      cat_comp := @compFunctor;
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  unfold eqFunctor.
  intros.
  unfold compFunctor, fmap.
  simpl.
  fold (fmap x0 f).
  fold (fmap y0 f).
  fold (fmap x (fmap x0 f)).
  fold (fmap y (fmap y0 f)).

  assert (hequality (hsetoid c) (fmap x (fmap x0 f)) (fmap x (fmap y0 f))).
  {
    apply fmorphism_preserve_hequality.
    apply (H0 _ _ f).
  }
  assert (hequality (hsetoid c) (fmap x (fmap y0 f)) (fmap y (fmap y0 f))).
  {
    apply (H _ _ (fmap y0 f)).
  }

  apply (htrans H1 H2).
Defined.
Next Obligation.
  constructor.
  - intros.
    constructor.
    intro.
    apply H.
  - intro.
    generalize (heq_extending_eq H).
    intro.
    destruct H0.
    destruct x.
    intro.
    unfold Setoids.extend in e.
    rewrite <- eq_rect_eq in e.
    rewrite <- eq_rect_eq in e.
    apply e.
Defined.
Next Obligation.
  intro.
  intros.
  unfold fmap, compFunctor. simpl.
  unfold fmap. simpl.
  apply hrefl.
Defined.
Next Obligation.
  intro.
  intros.
  unfold fmap. simpl.
  unfold idFunctor, fmap. simpl.
  apply hrefl.
Defined.
Next Obligation.
  intro.
  intros.
  unfold fmap; simpl.
  unfold idFunctor, fmap; simpl.
  apply hrefl.
Defined.
  

