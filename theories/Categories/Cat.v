Require Import Morphisms.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Inductive Heq_hom_naive {C : Category} {a b : C} (f : hom a b) : forall {c d}, hom c d → Prop :=
| mk_Heq_hom_naive : forall {g : hom a b}, f == g → Heq_hom_naive f g.

Notation "f ∼ g 'in' C" := (@Heq_hom_naive C _ _ f _ _ g) (at level 70, g at next level).
Infix "≈" := Heq_hom_naive (at level 70, only parsing).

Definition eqFunctor {C D} (F G : Functor C D) :=
  ∀ {a b} (f : a ⟶ b), fmap F f ≈ fmap G f.

Notation "F ==f G" := (eqFunctor F G) (at level 40).

Instance eqFunctor_equiv {C D} : Equivalence (@eqFunctor C D).
Proof.
  constructor.
  - unfold Reflexive.
    intro.
    constructor.
    reflexivity.
  - unfold Symmetric.
    intros.
    unfold eqFunctor.
    intros.
    unfold eqFunctor in H.
    destruct (H a b f).
    constructor.
    symmetry.
    exact H0.
  - unfold Transitive.
    intros.
    unfold eqFunctor.
    intros.
    destruct (H0 a b f).
    destruct (H a b f).
    constructor.
    rewrite H2, H1.
    reflexivity.
Defined.

Lemma eqFunctor_obj {C D} {F F' : Functor C D} : F ==f F' → forall a, F a = F' a.
Proof.
  intros.
  destruct (H a a identity).
  reflexivity.
Qed.

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
  

