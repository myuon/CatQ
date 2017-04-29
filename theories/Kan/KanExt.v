Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat Concrete.
From CatQ.Functors Require Import Concrete Bifunctor.
Require Import CatQ.Adjoint CatQ.Limit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure Lan {C D U} (F : Functor C D) (E : Functor C U) :=
  {
    lan_functor : Functor D U;
    lan_unit : Nat E (lan_functor ∘f F);
    is_lan :
      forall (S : Functor D U) (θ : Nat E (S ∘f F)),
        ∃! (τ : Nat lan_functor S) in [D,U], θ == (τ ⋆f F) ∘n lan_unit in [C,U];
  }.

Notation "F † E" := (Lan F E) (at level 50).
Notation "[lan: T 'with' η 'as' F 'along' E ]" := (@Build_Lan _ _ _ F E T η _).
Notation "[lan: T 'with' η  ]" := [lan: T with η as _ along _].
Notation "[lan: T ]" := [lan: T with _].
Notation "⟨lan: S 'with' θ 'of' kan ⟩" := ⟨exist: is_lan kan (S:=S) θ⟩.
Notation "⟨lan: θ 'of' kan ⟩" := ⟨lan: _ with θ of kan⟩.
Notation "⟨lan: θ ⟩" := ⟨lan: θ of _⟩.

Lemma lan_mediating_prop {C D U F E} (kan : @Lan C D U F E) {S θ} :
  θ == (⟨lan: S with θ of kan⟩ ⋆f F) ∘n lan_unit kan in [C,U].
Proof.
  destruct (is_lan kan θ).
  simpl.
  destruct u.
  intro.
  rewrite (H A).
  simpl.
  reflexivity.
Qed.

Lemma lan_mediating_prop_at {C D U F E} (kan : @Lan C D U F E) {S θ A} :
  component θ A == ⟨lan: S with θ of kan⟩ (F A) ∘ lan_unit kan A.
Proof.
  apply (lan_mediating_prop kan).
Qed.

Lemma lan_mediating_unique {C D U F E} (kan : @Lan C D U F E) {S θ} :
  forall τ, (θ == (τ ⋆f F) ∘n lan_unit kan in [C,U]) → τ == ⟨lan: S with θ of kan⟩ in [D,U].
Proof.
  intros.
  destruct (is_lan kan θ).
  simpl.
  destruct u.
  intro.
  symmetry.
  apply (H1 τ).
  rewrite H.
  reflexivity.
Qed.

Lemma lan_mediating_unique_at {C D U F E} (kan : @Lan C D U F E) {S θ} {A} :
  forall τ, (θ == (τ ⋆f F) ∘n lan_unit kan in [C,U]) → τ A == ⟨lan: S with θ of kan⟩ A.
Proof.
  intros.
  apply (lan_mediating_unique H).
Qed.

Program Definition Lan_f {C D U F} (kan : forall E, F † E) : Functor ([C,U]) ([D,U]) :=
  [fmap: fun E E' α => ⟨lan: lan_functor (kan E') with lan_unit (kan E') ∘n α of kan E⟩
   with fun (E : [C,U]) => (lan_functor (kan E) : [D,U])].
Next Obligation.
  unfold Proper, respectful.
  intros.
  apply (lan_mediating_unique_at (θ:=lan_unit (kan b) ∘n y)).
  rewrite <- (lan_mediating_prop (kan a) (θ:=lan_unit (kan b) ∘n x)).
  intro.
  simpl.
  rewrite (H A0).
  reflexivity.
Defined.
Next Obligation.
  symmetry.
  rewrite <- (lan_mediating_unique_at (θ:=lan_unit (kan a) ∘n idNat a) (τ:=idNat _)).
  - simpl.
    reflexivity.
  - simpl.
    intro.
    rewrite right_id_of.
    rewrite left_id_of.
    reflexivity.
Defined.
Next Obligation.
  symmetry.
  rewrite <- (lan_mediating_unique_at (θ:=lan_unit (kan c) ∘n g ∘ f) (τ:=⟨lan: lan_functor (kan c) with lan_unit (kan c) ∘n g of kan b ⟩ ∘ ⟨lan: lan_functor (kan b) with lan_unit (kan b) ∘n f of kan a ⟩)).
  - simpl.
    reflexivity.
  - simpl.
    intro.
    refine
      (`begin
        lan_unit (kan c) A0 ∘ (g A0 ∘ f A0)
       =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
        (lan_unit (kan c) A0 ∘ g A0) ∘ f A0
       =⟨ hom_refl ⟩
        (lan_unit (kan c) ∘n g) A0 ∘ f A0
       =⟨ ltac: (rewrite (lan_mediating_prop_at (kan b)); reflexivity) ⟩
        (⟨lan: lan_unit (kan c) ∘n g⟩ (F A0) ∘ lan_unit (kan b) A0) ∘ f A0
       =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
        ⟨lan: lan_unit (kan c) ∘n g⟩ (F A0) ∘ (lan_unit (kan b) A0 ∘ f A0)
       =⟨ hom_refl ⟩
        ⟨lan: lan_unit (kan c) ∘n g⟩ (F A0) ∘ (lan_unit (kan b) ∘n f) A0
       =⟨ ltac: (rewrite (lan_mediating_prop_at (kan a)); reflexivity) ⟩
        ⟨lan: lan_unit (kan c) ∘n g⟩ (F A0) ∘ (⟨lan: lan_unit (kan b) ∘n f⟩ (F A0) ∘ lan_unit (kan a) A0)
       =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
        (⟨lan: lan_unit (kan c) ∘n g⟩ (F A0) ∘ ⟨lan: lan_unit (kan b) ∘n f⟩ (F A0)) ∘ lan_unit (kan a) A0
        `end).
Defined.

Program Definition inv {C D U} (F : Functor C D) : Functor ([D,U]) ([C,U]) :=
  [fmap: fun _ _ α => α ⋆f F with fun (G : [D,U]) => (G ∘f F : [C,U]) ].
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Definition adjoint_Lan_Inv {C D U F} (F_has_kan : forall E, F † E) : [adjoint: Lan_f F_has_kan , inv F as [C,U] to [D,U] ] :=
  {|
    adjunction := [Nat: fun ES => [mapoid: fun θ => (θ ⋆f F) ∘n lan_unit (F_has_kan (fst ES))] ];
  |}.
Next Obligation.
  simpl.
  unfold opposite_obj_to, opposite_obj.
  unfold Proper, respectful.
  simpl.
  intros.
  rewrite (H (F A)).
  reflexivity.
Defined.
Next Obligation.
  constructor.
  simpl.
  intros.
  unfold opposite_obj in x.
  unfold Lan_f, opf, op_trf; simpl.
  unfold fmap; simpl.
  unfold fmap; simpl.
  unfold opposite_obj, opposite_hom.
  unfold opposite_hom_to.
  rewrite assoc_of.
  rewrite assoc_of.
  rewrite assoc_of.
  rewrite <- (lan_mediating_prop_at (F_has_kan (fst b)) (θ:=lan_unit (F_has_kan (fst a)) ∘n fst f) (A:=A)).
  rewrite <- assoc_of.
  simpl.
  reflexivity.
Defined.
Next Obligation.
  unfold natiso.
  intro.
  refine (exist _ (([Nat: fun ES => [mapoid: fun (α : fst ES ⟶ (snd ES ∘f F) in [C,U]) => ⟨lan: snd ES with α of F_has_kan (fst ES)⟩]
                     as (homFunctor ∘f ⟨ProductF: idFunctor,inv F⟩)
                     to (homFunctor ∘f ⟨ProductF: opf (Lan_f F_has_kan),idFunctor⟩)] : @hom [(opposite ([C,U]) × ([D,U])),Setoids] _ _) a) _).
  {
    simpl.
    split.
    - intros.
      rewrite <- (lan_mediating_prop_at (F_has_kan (fst a)) (θ:=x)).
      reflexivity.
    - intros.
      symmetry.
      apply (lan_mediating_unique_at (kan:=F_has_kan (fst a)) (θ:=(x ⋆f F) ∘n lan_unit (F_has_kan (fst a)))).
      reflexivity.
  }
  Unshelve.
  - unfold Proper, respectful.
    simpl.
    intros.
    apply (lan_mediating_unique_at (θ:=y)).
    simpl; intro.
    rewrite <- H.
    apply (lan_mediating_prop_at (F_has_kan (fst ES))).
  - simpl.
    constructor.
    simpl.
    intros.
    unfold opf, op_trf, Lan_f; simpl.
    unfold fmap; simpl.
    unfold fmap; simpl.
    unfold opposite_hom, opposite_hom_to, opposite_obj, opposite_obj_to.
    rewrite <- (lan_mediating_unique_at (θ:=((snd f ⋆f F) ∘{[C, U]} x) ∘{[C, U]} fst f) (A:=A) (τ:=snd f ∘n ⟨lan: x ⟩ ∘n ⟨lan: lan_unit (F_has_kan (fst a0)) ∘n fst f ⟩)).
    + simpl.
      reflexivity.
    + simpl; intro.
      repeat rewrite assoc_of.
      rewrite <- (lan_mediating_prop_at (F_has_kan (fst b)) (θ:=lan_unit (F_has_kan (fst a0)) ∘n fst f) (A:=A0)).
      simpl.
      rewrite <- (assoc_of (h:=⟨lan: x ⟩ (F A0))).
      rewrite <- (lan_mediating_prop_at (F_has_kan (fst a0))).
      reflexivity.
Defined.

Program Definition const_at_One {J C} {F : Functor One C} : Nat (F ∘f Δ[J](tt : One)) Δ[J](F tt)
  := [Nat: fun a => identity].
Next Obligation.
  constructor.
  intros.
  rewrite right_id_of, left_id_of.
  unfold const, compFunctor, fmap; simpl.

  assert (fmap F (tt : @hom One tt _) == fmap F identity).
  reflexivity.

  rewrite H.
  rewrite fmap_identity.
  reflexivity.
Defined.

Program Definition const_at_One_inv {J C} {F : Functor One C} : Nat Δ[J](F tt) (F ∘f Δ[J](tt : One))
  := [Nat: fun a => identity].
Next Obligation.
  constructor.
  intros.
  rewrite right_id_of, left_id_of.
  unfold const, compFunctor, fmap; simpl.

  assert (fmap F (tt : @hom One tt _) == fmap F identity).
  reflexivity.

  rewrite H.
  rewrite fmap_identity.
  reflexivity.
Defined.

Program Definition colim_as_Lan_along_One {C D} {F : Functor C D} : Δ[C](tt : One)†F ≃ Colimit F in Types
  := [iso: fun lan => [colimit: lan_functor lan tt
                     with (const_at_One ∘n lan_unit lan : @hom [C,D] _ _) of (F : [C,D])]
      with fun colim => [lan: [fmap: fun _ _ tt => identity with fun tt => colim_object colim]
                       with [Nat: fun a => colim_cone colim a] ] ].
Next Obligation.
  destruct (is_lan lan (const_at_One_inv (F:=Δ(v)) ∘n (cocone : Nat F _))).
  destruct u.
  exists (x tt).
  constructor.
  - intro.
    simpl in H.
    generalize (H A); intro.
    rewrite left_id_of.
    rewrite <- H1.
    rewrite left_id_of.
    reflexivity.
  - intros.
    apply (H0 (One_lift (g : _ ⟶ Δ(v) tt in D))).
    simpl.
    intro.
    generalize (H1 A); intro.
    rewrite left_id_of in H2.
    rewrite H2.
    rewrite left_id_of.
    reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  rewrite right_id_of.
  reflexivity.
Defined.
Next Obligation.
  constructor.
  intros.
  rewrite (@compFunctor_compose _ _ _ _ Δ[C](tt : One)).
  rewrite fmap_of_fmap.
  rewrite <- (naturality_of (colim_cone colim)).
  reflexivity.
Defined.
Next Obligation.
  destruct colim.
  destruct (is_colimit (S tt) (const_at_One ∘n θ : F ⟶ Δ[C](S tt) in [C,D])).
  exists (One_lift (x : _ tt ⟶ S tt in D) : _ ⟶ S in [One,D]).
  simpl.
  constructor.
  - intro.
    destruct u.
    refine
      (`begin
        θ A
       ↑⟨ left_id_of ⟩
        const_at_One A ∘ θ A
       =⟨ hom_refl ⟩
        (const_at_One ∘n θ) A
       ↑⟨ H A ⟩
        (fmap Δ x ∘n colim_cone) A
       =⟨ hom_refl ⟩
        (One_lift (x : Δ(_) tt ⟶ _)) tt ∘ colim_cone A
       `end).
  - intros.
    destruct u.
    simpl; intro.
    destruct A.
    eapply H1.
    simpl.
    simpl in H0.
    intro.
    rewrite <- (H A).
    rewrite left_id_of.
    reflexivity.
Qed.

