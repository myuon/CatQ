Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
Require Import CatQ.Categories.Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition const {C D : Category} (a : C) : Functor D C :=
  [fmap: fun _ _ _ => identity with fun _ => a ].
Next Obligation.
  unfold Proper, respectful.
  intros.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  rewrite left_id_of.
  reflexivity.
Defined.

Definition const_one {C : Category} (a : C) : Functor One C := const a.

Notation "Δ[ D ]( a )" := (@const _ D a).
Notation "Δ( a )" := (const_one a).

Program Definition One_lift {D} {F G : Functor One D} (h : F tt ⟶ G tt in D) : Nat F G
  := [Nat: fun t => match t with
                   | tt => h
                   end ].
Next Obligation.
  constructor.
  intros.
  destruct a, b.

  assert (f == identity).
  destruct f.
  reflexivity.

  rewrite H.
  rewrite fmap_identity, fmap_identity.
  rewrite right_id_of, left_id_of.
  reflexivity.
Defined.

Lemma functor_to_One_unique {C} {F : Functor C One} : F ==f Δ[C](tt : One).
Proof.
  assert (forall x, F x = tt).
  { intro; destruct (F x); exact eq_refl. }

  exists H.
  intros.
  destruct (fmap F f).
  reflexivity.
Qed.

Program Definition op_trf {C D} (F : Functor (opposite C) D) : Functor C (opposite D) :=
  [fmap: fun a b f => opposite_hom_to (fmap F (opposite_hom_to f)) with fun a => opposite_obj_to (F a) as C to opposite D].
Next Obligation.
  unfold opposite_hom_to, opposite_obj_to.
  solve_proper.
Defined.
Next Obligation.
  assert (forall a, opposite_hom_to (@identity C a) = @identity (opposite C) a).
  reflexivity.

  rewrite (H _).
  unfold opposite_hom_to.
  apply fmap_identity.
Defined.
Next Obligation.
  refine
    (`begin
      opposite_hom_to (fmap F (opposite_hom_to (g ∘{C} f)))
     =⟨ _ ⟩
      opposite_hom_to (fmap F (opposite_hom_to f ∘{opposite C} opposite_hom_to g))
     =⟨ _ ⟩
      opposite_hom_to (fmap F (opposite_hom_to f) ∘{D} fmap F (opposite_hom_to g))
     =⟨ _ ⟩
      opposite_hom_to (fmap F (opposite_hom_to g)) ∘{opposite D} opposite_hom_to (fmap F (opposite_hom_to f))
     `end).

  - apply (@is_setoid (@morphism (opposite D) _ _)).
  - unfold opposite_hom_to.
    simpl.
    apply fmap_compose.
  - apply (@is_setoid (@morphism (opposite D) _ _)).
Defined.

Program Definition opopf {C} : Functor C (opposite (opposite C)) :=
  [fmap: fun _ _ f => (opposite_hom_to (opposite_hom_to f)) with fun a => opposite_obj_to (opposite_obj_to a)].
Next Obligation.
  unfold opposite_obj_to, opposite_hom_to.
  solve_proper.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Definition opop_invf {C} : Functor (opposite (opposite C)) C :=
  [fmap: fun _ _ f => (opposite_hom (opposite_hom f)) with fun a => opposite_obj (opposite_obj a)].
Next Obligation.
  unfold opposite_obj_to, opposite_hom_to.
  solve_proper.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Definition opf {C D} (F : Functor C D) : Functor (opposite C) (opposite D) := @op_trf (opposite C) D (F ∘f opop_invf).


