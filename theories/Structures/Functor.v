Require Import Morphisms Setoid RelationClasses.
Require Import Utf8.
Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Setoids Category Morphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

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

Notation "[fmorphism: fa 'with' fo 'as' C 'to' D 'by' prf ]" := (@Build_Functor C D fo fa prf).
Notation "[fmorphism: fa 'with' fo 'as' C 'to' D ]" := [fmorphism: fa with fo as C to D by _].
Notation "[fmorphism: fa 'with' fo ]" := [fmorphism: fa with fo as _ to _ ].
Notation "[fmorphism: fa ]" := [fmorphism: fa with _ as _ to _ ].

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

Lemma fmap_proper {C D : Category} (F : Functor C D) {a b : C} :
  Proper (@equality _ ==> @equality _) (fmap F (a:=a) (b:=b)).
Proof.
  solve_proper.
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
    [fmorphism: fun _ _ => [mapoid: funct_map ftype by funct_map_proper ftype] with funct_obj ftype].
Next Obligation.
  apply Build_Is_Functor.
  - simpl. intro.
    apply funct_identity.
  - simpl. intros.
    apply funct_compose.
Defined.

Notation "[fmap: fa 'with' fo 'as' C 'to' D ]" := (Build_Functor_from_Type (@Build_Functor_Type C D fo fa _ _ _)).
Notation "[fmap: fa 'with' fo ]" := [fmap: fa with fo as _ to _ ].

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

Program Definition idFunctor {C : Category} : Functor C C :=
  [fmap: fun _ _ f => f with fun a => a as C to C].
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Definition compFunctor {C D E : Category} (G : Functor D E) (F : Functor C D) : Functor C E :=
  [fmap: fun _ _ f => fmap G (fmap F f) with fun a => fobj G (fobj F a)].
Next Obligation.
  solve_proper.
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

Notation "F ∘f G" := (compFunctor F G) (at level 40).

Lemma compFunctor_compose {C D E} (G : Functor D E) (F : Functor C D) {a b} (f : a ⟶ b) :
  fmap (G ∘f F) f == fmap G (fmap F f).
Proof.
  reflexivity.
Qed.

Definition full {C D : Category} (F : Functor C D) : Prop := forall {a b}, surj (@fmorphism C D F a b).
Definition faithful {C D : Category} (F : Functor C D) : Prop := forall {a b}, inj (@fmorphism C D F a b).

(* ff = iso on hom *)
Definition ff {C D : Category} (F : Functor C D) : Type
  := forall {a b}, (morphism a b) ≃ (morphism (F a) (F b)) in Setoids.


