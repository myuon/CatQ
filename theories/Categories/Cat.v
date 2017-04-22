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
  intros.
  unfold compFunctor, fmap.
  simpl.
  fold (fmap x0 f).
  fold (fmap y0 f).
  fold (fmap x (fmap x0 f)).
  fold (fmap y (fmap y0 f)).
  destruct (H0 a0 b0 f).
  destruct (H _ _ g).
  constructor.
  rewrite H1.
  exact H2.
Defined.
Next Obligation.
  constructor.
  unfold fmap, compFunctor. simpl.
  unfold fmap. simpl.
  reflexivity.
Defined.
Next Obligation.
  constructor.
  unfold fmap. simpl.
  unfold idFunctor, fmap. simpl.
  reflexivity.
Defined.
Next Obligation.
  constructor.
  unfold fmap; simpl.
  unfold idFunctor, fmap; simpl.
  reflexivity.
Defined.
  

