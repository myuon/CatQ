Require Import Morphisms.
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
      cat_identity := @idFunctor;
      cat_comp := @compFunctor;
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  unfold eqFunctor.
  destruct H, H0.
  
  assert (∀ x3 : a, (x ∘f x0) x3 = (y ∘f y0) x3).
  { intro; simpl.
    rewrite x1, x2.
    reflexivity. }
  exists H.
  intros.
  rewrite (compFunctor_compose y y0 f).
  rewrite (compFunctor_compose x x0 f).
  rewrite <- e0.
  rewrite <- e.

  rewrite fmap_preserve_extend.
  rewrite extend_trans.
  apply extend_irrelevance.
Defined.
Next Obligation.
  unfold eqFunctor.
  exists (fun t => eq_refl).
  intros.
  rewrite extend_eq.
  reflexivity.
Defined.
Next Obligation.
  unfold eqFunctor.
  exists (fun t => eq_refl).
  intros.
  rewrite extend_eq.
  reflexivity.
Defined.
Next Obligation.
  unfold eqFunctor.
  exists (fun t => eq_refl).
  intros.
  rewrite extend_eq.
  reflexivity.
Defined.

