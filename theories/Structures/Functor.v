Require Import Morphisms Setoid.
Require Import Utf8.
Require Import CatQ.Structures.Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(* Functor *)
Class Is_Functor
      (fdom fcod : Category)
      (fobj : fdom → fcod)
      (fmorphism : forall {a b}, @morphism fdom a b -⇒ @morphism fcod (fobj a) (fobj b)) :=
  {
    fmorphism_identity : forall {a}, fmorphism (@identity fdom a) == @identity fcod (fobj a);
    fmorphism_compose : forall {a b c} {f : a ⟶ b} {g : b ⟶ c}, fmorphism (compose (g,f)) == compose (fmorphism g, fmorphism f);
  }.

Structure Functor (fdom fcod : Category) :=
  {
    fobj :> fdom → fcod;
    fmorphism : forall {a b}, @morphism fdom a b -⇒ @morphism fcod (fobj a) (fobj b);
    is_functor :> Is_Functor (@fmorphism);
  }.
Existing Instance is_functor.

Definition fmap {C D : Category} (F : Functor C D) :
  forall {a b}, hom a b → hom (fobj F a) (fobj F b) := fun _ _ => fmorphism F.

Lemma fmap_identity {C D : Category} (F : Functor C D) :
  forall {a}, fmap F (@identity C a) == @identity D (F a).
Proof.
  unfold fmap. intro.
  apply fmorphism_identity.
Defined.

Lemma fmap_compose {C D : Category} (F : Functor C D) :
  forall {a b c} {g : b ⟶ c} {f : a ⟶ b}, fmap F (g ∘ f) == fmap F g ∘ fmap F f.
Proof.
  unfold fmap. intros.
  apply fmorphism_compose.
Defined.

Structure Functor_Type (fdom fcod : Category) :=
  {
    funct_obj : fdom → fcod;
    funct_map : forall {a b}, hom a b → hom (funct_obj a) (funct_obj b);
    funct_map_proper : forall {a b}, Proper ((@equality _) ==> (@equality _)) (@funct_map a b);
    funct_identity : forall {a}, funct_map (@identity fdom a) == @identity fcod (funct_obj a);
    funct_compose : forall {a b c} {f : hom a b} {g : hom b c}, funct_map (g ∘ f) == funct_map g ∘ funct_map f;
  }.

Program Definition Build_Functor_from_Type : forall {C D}, Functor_Type C D → Functor C D :=
  fun C D ftype =>
    {|
      fobj := funct_obj ftype;
      fmorphism := fun _ _ =>
        {|
          mapping := funct_map ftype;
          is_mapoid := funct_map_proper ftype;
        |};
    |}.
Next Obligation.
  apply Build_Is_Functor.
  - simpl. intro.
    apply funct_identity.
  - simpl. intros.
    apply funct_compose.
Defined.

Program Definition Destruct_to_Functor_Type : forall {C D}, Functor C D → Functor_Type C D :=
  fun C D functor =>
    {|
      funct_obj := fobj functor;
      funct_map := fun _ _ => fmap functor;
      funct_map_proper := fun _ _ => is_mapoid (fmorphism functor);
    |}.
Next Obligation.
  apply fmorphism_identity.
Defined.
Next Obligation.
  apply fmorphism_compose.
Defined.

Program Definition compFunctor {C D E : Category} (F : Functor C D) (G : Functor D E) : Functor C E :=
  Build_Functor_from_Type
    {|
      funct_obj := fun a => fobj G (fobj F a);
      funct_map := fun _ _ f => fmap G (fmap F f);
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  setoid_rewrite fmorphism_identity.
  setoid_rewrite fmorphism_identity.
  reflexivity.
Defined.
Next Obligation.
  setoid_rewrite fmorphism_compose.
  setoid_rewrite fmorphism_compose.
  reflexivity.
Defined.

