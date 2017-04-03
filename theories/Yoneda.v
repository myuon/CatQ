Require Import Morphisms Setoid.
Require Import Utf8.
Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Category Functor Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(* FunCat *)
Program Definition FunCat (C D : Category) : Category :=
  Build_Category_from_Type
    {|
      cat_object := Functor C D;
      cat_hom := Nat;
      cat_hom_equal := fun _ _ α β => forall A, component α A == component β A;
      cat_identity := idNat;
      cat_comp := fun _ _ _ => compNat;
    |}.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive.
    reflexivity.
  - unfold Symmetric.
    symmetry. apply H.
  - unfold Transitive.
    intros. rewrite H, H0. reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful.
  intros.
  unfold equality. simpl.
  rewrite H, H0.
  reflexivity.
Defined.
Next Obligation.
  apply assoc_of.
Defined.
Next Obligation.
  apply left_identity.
Defined.
Next Obligation.
  apply right_identity.
Defined.

Notation "[ C , D ]" := (FunCat C D) (at level 50).

Notation "PSh[ C ]" := (FunCat (opposite C) Setoids) (at level 50).

(* contravariant Hom functor *)
Program Definition contraHomFunctor {C : Category} (a : C) : Functor (opposite C) Setoids :=
  Build_Functor_from_Type
    {|
      funct_obj := fun (y : opposite C) => (@morphism C y a : object Setoids);
      funct_map :=
        fun x y (f : @morphism (opposite C) x y) =>
          {|
            mapping := fun (xa : @morphism C x a) => xa ∘ f;
          |};
    |}.
Next Obligation.
  unfold Func.flip in f.
  unfold Proper, respectful.
  intros.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful. simpl.
  intros.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  apply right_identity.
Defined.
Next Obligation.
  rewrite assoc_of.
  reflexivity.
Defined.

Program Definition contraHomNat {C : Category} {a b : C} (t : hom a b) : Nat (contraHomFunctor a) (contraHomFunctor b) :=
  {|
    component :=
      fun x =>
        {|
          mapping := fun xa => t ∘ xa;
        |};
  |}.
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  apply Build_Is_Nat.
  simpl. intros.
  apply associativity.
Defined.

(* Yoneda functor *)
Program Definition yoneda {C : Category} : Functor C (PSh[C]) :=
  Build_Functor_from_Type
    {|
      funct_obj := fun a => (contraHomFunctor a : object (PSh[C]));
      funct_map := fun _ _ => contraHomNat;
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  unfold contraHomNat. simpl.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  apply left_identity.
Defined.
Next Obligation.
  apply associativity.
Defined.

Structure isomorphic {C : Category} (x y : C) :=
  {
    iso_right : hom x y;
    iso_left : hom y x;
    iso_on_left : iso_left ∘ iso_right == identity;
    iso_on_right : iso_right ∘ iso_left == identity;
  }.

Notation "A ≃ B 'at' C" := (@isomorphic C A B) (at level 50).
Notation "A ≃ B" := (isomorphic A B) (at level 60).

Program Definition YonedaLemma_right {C : Category} {a : C} {F : PSh[C]} : @morphism (PSh[C]) (yoneda a) F -⇒ F a :=
  {|
    mapping := fun yaF => yaF a identity;
  |}.
Next Obligation.
  solve_proper.
Defined.

Program Definition YonedaLemma_left {C : Category} {a : C} {F : PSh[C]} : F a -⇒ @morphism (PSh[C]) (yoneda a) F :=
  {|
    mapping := fun Fa =>
      {|
        component := fun b =>
          {|
            mapping := fun ba => fmap F ba Fa;
          |};
      |};
  |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  assert (fmap F x == fmap F y).
  - rewrite H.
    reflexivity.
  - destruct F.
    unfold fmap.
    simpl.
    unfold fmap in H0.
    simpl in H0.
    apply H0.
Defined.
Next Obligation.
  apply Build_Is_Nat.
  simpl. intros.
  assert (fmap F f ∘ fmap F x == fmap F (x ∘ f)).
  - rewrite <- (fmap_compose F).
    reflexivity.
  - rewrite <- (mapoid_apply _ H).
    simpl.
    reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful. simpl.
  intros.
  rewrite H.
  reflexivity.
Defined.

Lemma Yoneda {C : Category} {a : C} {F : PSh[C]} : @morphism (PSh[C]) (yoneda a) F ≃ F a at Setoids.
Proof.
  apply (@Build_isomorphic _ _ _ (YonedaLemma_right : @hom Setoids _ _) (YonedaLemma_left : @hom Setoids _ _)).
  - unfold YonedaLemma_right, YonedaLemma_left.
    simpl. intros.
    assert (fmap F x0 ∘ x a == x A ∘ fmap (contraHomFunctor a) x0).
    + apply (naturality_of x).
    + exact
        (`begin
          fmap F x0 ((x a) identity)
         =⟨ ltac: (apply Setoids_comp_apply) ⟩
          (fmap F x0 ∘ x a) identity
         =⟨ mapoid_apply identity H ⟩
          (x A ∘ fmap (contraHomFunctor a) x0) identity
         =⟨ ltac: (apply Setoids_comp_apply) ⟩
          (x A) (fmap (contraHomFunctor a) x0 identity)
         =⟨ mapoid_cong (x A) (ltac: (unfold contraHomFunctor, fmap; simpl; reflexivity)) ⟩
          (x A) (identity ∘ x0)
         =⟨ ltac: (rewrite left_id_of; reflexivity) ⟩
          (x A) x0
          `end).
  - unfold YonedaLemma_right, YonedaLemma_left.
    simpl.
    intros.
    unfold FunCat; simpl in F.
    exact
      (`begin
        (fmap F identity) x
       =⟨ mapoid_apply x (fmap_identity F) ⟩
        x
       `end).
Qed.
    

