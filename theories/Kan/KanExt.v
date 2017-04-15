Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat.
Require Import CatQ.Adjoint.

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
        ∃! (τ : Nat lan_functor S) in [D,U], θ == (τ ⋆f F) ∘n lan_unit in @morphism [C,U] _ _;
  }.

Notation "F † E" := (Lan F E) (at level 50).
Notation "[lan: T 'with' η 'as' F 'along' E ]" := (@Build_Lan _ _ _ F E T η _).
Notation "[lan: T 'with' η  ]" := [lan: T with η as _ along _].
Notation "[lan: T ]" := [lan: T with _].
Notation "⟨lan: S 'with' θ 'of' kan ⟩" := ⟨exist: is_lan kan (S:=S) θ⟩.
Notation "⟨lan: θ 'of' kan ⟩" := ⟨lan: _ with θ of kan⟩.
Notation "⟨lan: θ ⟩" := ⟨lan: θ of _⟩.

Lemma lan_mediating_prop {C D U F E} (kan : @Lan C D U F E) {S θ} :
  θ == (⟨lan: S with θ of kan⟩ ⋆f F) ∘n lan_unit kan in @morphism [C,U] _ _.
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
  forall τ, (θ == (τ ⋆f F) ∘n lan_unit kan in @morphism [C,U] _ _) → τ == ⟨lan: S with θ of kan⟩ in @morphism [D,U] _ _.
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
  forall τ, (θ == (τ ⋆f F) ∘n lan_unit kan in @morphism [C,U] _ _) → τ A == ⟨lan: S with θ of kan⟩ A.
Proof.
  intros.
  apply (lan_mediating_unique H).
Qed.

Program Definition Lan_f {C D U F} (kan : forall E, F † E) : Functor [C,U] [D,U] :=
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

Program Definition inv {C D U} (F : Functor C D) : Functor [D,U] [C,U] :=
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

