Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category Functor.
From CatQ.Categories Require Import Product.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Definition Bifunctor (C D E : Category) := Functor (Product C D) E.

Program Definition homFunctor {C : Category} : Bifunctor (opposite C) C Setoids :=
  Build_Functor_from_Type
    {|
      funct_obj := fun (a : object (Product (opposite C) C)) => (@morphism C (fst a) (snd a) : object Setoids);
      funct_map :=
        fun a b (ab : a ⟶ b) =>
          {| mapping := fun (f : @hom C (fst a) (snd a)) => snd ab ∘ f ∘ fst ab; |};
    |}.
Next Obligation.
  simpl.
  unfold Proper, respectful.
  intros.
  destruct ab.
  simpl.
  simpl in c, c0.
  unfold Func.flip in c.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful, Func.flip.
  simpl.
  intros.
  destruct x, y.
  destruct H.
  simpl in H, H0.
  simpl.
  rewrite H, H0.
  reflexivity.
Defined.
Next Obligation.
  simpl in x.
  unfold comp.
  rewrite right_identity.
  rewrite left_identity.
  reflexivity.
Defined.
Next Obligation.
  destruct f, g.
  simpl in c, c0, c1, c2, x.
  unfold Func.flip in c, c1.
  repeat rewrite assoc_of.
  reflexivity.
Defined.

Definition bimap {C D E} (G : Bifunctor C D E) {a b : Product C D} (f : fst a ⟶ fst b) (g : snd a ⟶ snd b) : G a ⟶ G b
  := fmap G (Spair f g).


