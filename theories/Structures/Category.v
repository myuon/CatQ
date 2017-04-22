Require Import Morphisms Setoid Vectors.Fin ProofIrrelevance.
Require Import Utf8.

Require Program.Basics.
Module Func := Basics.

Add LoadPath "../../theories" as CatQ.
Require Import CatQ.Structures.Setoids.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(* Category *)
Class Is_Category
      (object: Type)
      (morphism: object → object → Setoid)
      (hsetoid: HSetoid morphism)
      (identity: ∀ {x}, carrier (morphism x x))
      (compose: ∀ {a b c}, morphism b c ** morphism a b -⇒ morphism a c) :=
  {
    eq_extend:
      forall a b (f g : morphism a b), @equality (morphism a b) f g <-> hequality hsetoid f g;
    associativity:
      ∀ a b c d (f: morphism a b) (g: morphism b c) (h: morphism c d),
        compose (| compose (| h , g |) , f |) == compose (| h , compose (| g , f |) |);
    left_identity:
      ∀ a b (f: morphism a b), compose (| identity , f |) == f;
    right_identity:
      ∀ a b (f: morphism a b), compose (| f , identity |) == f;
  }.

Structure Category :=
  {
    object :> Type;
    morphism : object → object → Setoid;
    hsetoid : HSetoid morphism;
    identity : ∀ {x}, carrier (morphism x x);
    compose : ∀ {a b c}, morphism b c ** morphism a b -⇒ morphism a c;
    is_category :> Is_Category (@hsetoid) (@identity) (@compose);
  }.
Existing Instance is_category.

Instance compose_proper (C : Category) :
  ∀ a b c, Proper ((@equality _) ==> (@equality _)) (@compose C a b c).
Proof.
  unfold Proper, respectful.
  intros.
  rewrite H.
  reflexivity.
Qed.

Definition hom (C : Category) : object C → object C → Type :=
  fun a b => carrier (morphism a b).

Notation "f == g 'in' C" := (@equality (@morphism C _ _) f g) (at level 70, g at next level).
Infix "==" := equality (at level 70, only parsing).
Notation "f ≈ g 'in' C" := (hequality (hsetoid C) f g) (at level 70, g at next level).
Infix "≈" := (hequality _) (at level 70, only parsing).

Definition comp (C : Category) : ∀ {a b c : C}, hom b c → hom a b → hom a c :=
  fun _ _ _ g f => compose (| g , f |).

Notation "A ⟶ B 'in' C" := (@hom C A B) (at level 60, B at next level, right associativity).
Infix "⟶" := hom (at level 60, only parsing).
Notation "g ∘ f" := (comp g f) (at level 30).
Notation "g ∘{ C } f" := (@comp C _ _ _ g f) (at level 30).

Lemma hom_refl : ∀ {C : Category} {a b : C} {f : a ⟶ b}, f == f.
Proof.
  reflexivity.
Qed.

Instance comp_proper {C : Category} {a b c : C} :
  Proper (@equality (morphism b c) ==> @equality (morphism a b) ==> @equality (morphism a c)) (fun g f => g ∘ f).
Proof.
  unfold comp, Proper, respectful.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma assoc_of (C : Category) :
  forall {a b c d : C} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d},
    (h ∘ g) ∘ f == h ∘ (g ∘ f).
Proof.
  intros.
  setoid_rewrite associativity.
  reflexivity.
Qed.

Lemma left_id_of (C : Category) :
  forall {a b : C} {f : a ⟶ b}, identity ∘ f == f.
Proof.
  intros.
  apply left_identity.
Qed.

Lemma right_id_of (C : Category) :
  forall {a b : C} {f : a ⟶ b}, f ∘ identity == f.
Proof.
  intros.
  apply right_identity.
Qed.

Structure Category_Type :=
  {
    cat_object : Type;
    cat_hom : cat_object → cat_object → Type;
    cat_identity : ∀ {x}, cat_hom x x;
    cat_comp : ∀ {a b c}, cat_hom b c → cat_hom a b → cat_hom a c;
    cat_hsetoid : HSetoid cat_hom;

    cat_hom_equal : ∀ {a b}, cat_hom a b → cat_hom a b → Prop;
    cat_hom_equal_equiv : ∀ {a b}, Equivalence (@cat_hom_equal a b);
    cat_comp_proper : ∀ {a b c}, Proper (cat_hom_equal ==> cat_hom_equal ==> cat_hom_equal) (@cat_comp a b c);

    cat_eq_extend : forall a b (f g : cat_hom a b), cat_hom_equal f g <-> hequality cat_hsetoid f g;
    cat_associativity : ∀ a b c d (f : cat_hom a b) (g : cat_hom b c) (h : cat_hom c d),
                          cat_hom_equal (cat_comp (cat_comp h g) f) (cat_comp h (cat_comp g f));
    cat_left_identity : ∀ a b (f : cat_hom a b),
                          cat_hom_equal (cat_comp cat_identity f) f;
    cat_right_identity : ∀ a b (f : cat_hom a b),
                          cat_hom_equal (cat_comp f cat_identity) f;
  }.

Program Definition Build_Category_from_Type : Category_Type → Category :=
  fun ctype =>
    {|
      object := cat_object ctype;
      morphism := fun X Y => [setoid: (@cat_hom ctype X Y) with (@cat_hom_equal ctype _ _)];
      hsetoid := cat_hsetoid ctype;
      identity := @cat_identity ctype;
      compose := fun a b c => [mapoid: fun ps => @cat_comp ctype _ _ _ (fst ps) (snd ps)];
    |}.
Next Obligation.
  apply cat_hom_equal_equiv.
Defined.
Next Obligation.
  unfold Proper, respectful.
  intros.
  destruct x, y, H.
  unfold fst, snd in H, H0.
  unfold fst, snd.
  apply cat_comp_proper.
  - exact H.
  - exact H0.
Defined.
Next Obligation.
  apply Build_Is_Category.
  - apply cat_eq_extend.
  - apply cat_associativity.
  - apply cat_left_identity.
  - apply cat_right_identity.
Defined.

Program Definition Destruct_to_Category_Type : Category → Category_Type :=
  fun C =>
    {|
      cat_object := object C;
      cat_identity := @identity C;
      cat_hom := fun a b => carrier (@morphism C a b);
      cat_hom_equal := fun a b => @equality (@morphism C a b);
      cat_hom_equal_equiv := fun a b => is_setoid (@morphism C a b);
      cat_hsetoid := hsetoid C;
      cat_comp := fun _ _ _ g f => @compose C _ _ _ (| g , f |);
    |}.
Next Obligation.
  apply eq_extend.
Defined.
Next Obligation.
  apply associativity.
Defined.
Next Obligation.
  apply left_identity.
Defined.
Next Obligation.
  apply right_identity.
Defined.

Program Definition opposite : Category → Category :=
  fun C => let Ctype := Destruct_to_Category_Type C in
    Build_Category_from_Type {|
      cat_object := cat_object Ctype;
      cat_hom := Func.flip (@cat_hom Ctype);
      cat_hom_equal := fun a b => @cat_hom_equal Ctype b a;
      cat_hom_equal_equiv := fun a b => @cat_hom_equal_equiv Ctype b a;
      cat_identity := @cat_identity Ctype;
      cat_comp := fun _ _ _ => Func.flip (@cat_comp Ctype _ _ _);
    |}.
Next Obligation.
  refine [hsetoid: fun a b c d f g => hequality (hsetoid C) f g].
  constructor.
  - intros; apply hrefl.
  - intros; apply (hsym H).
  - intros; apply (htrans H H0).
Defined.      
Next Obligation.
  unfold Proper, respectful, Func.flip.
  intros.
  rewrite H, H0.
  reflexivity.
Defined.
Next Obligation.
  unfold Func.flip in f,g.
  apply (eq_extend f g).
Defined.
Next Obligation.
  unfold Func.flip.
  symmetry.
  apply associativity.
Defined.
Next Obligation.
  unfold Func.flip.
  apply right_identity.
Defined.
Next Obligation.
  unfold Func.flip.
  apply left_identity.
Defined.

Definition opposite_obj {C : Category} : object (opposite C) → object C := fun x => x .
Definition opposite_hom {C : Category} {a b : opposite C} : @hom (opposite C) a b → @hom C b a := fun f => f.

Definition opposite_obj_to {C : Category} : object C → object (opposite C) := fun x => x .
Definition opposite_hom_to {C : Category} {a b : opposite C} : @hom C a b → @hom (opposite C) b a := fun f => f.

Program Definition Setoids : Category :=
  Build_Category_from_Type {|
      cat_object := Setoid;
      cat_hom := fun X Y => Mapoid X Y;
      cat_hom_equal := fun _ _ f g => forall x, f x == g x;
      cat_hsetoid := [hsetoid: fun _ _ _ _ f g => forall x, f x ≈ g x];
      cat_identity := fun _ => {| mapping := fun x => x |};
      cat_comp := fun _ _ _ g f => {| mapping := fun x => g (f x) |};
    |}.
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive.
    intros. reflexivity.
  - unfold Symmetric.
    intros. symmetry. apply H.
  - unfold Transitive.
    intros. rewrite H, H0. reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Defined.
Next Obligation.
  constructor.
  - intro.
    apply heqex_extend_eq.
    exact H.
  - intros.
    apply (@heqex_extend_eq Setoid Mapoid_space a b).
    exact H.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  reflexivity.
Defined.

Lemma mapoid_apply {S S'} (f g : @hom Setoids S S') (a : S) :
  (f == g) → (f a == g a).
Proof.
  intro.
  destruct f, g.
  simpl.
  simpl in H.
  apply H.
Qed.

Lemma mapoid_cong {S S'} (f : @hom Setoids S S') (a b : S) :
  (a == b) → (f a == f b).
Proof.
  intro.
  rewrite H.
  reflexivity.
Qed.

Lemma Setoids_comp_apply {a b c : Setoids} {f : a ⟶ b} {g : b ⟶ c} : forall x, (g ∘ f) x == g (f x).
Proof.
  intro.
  reflexivity.
Qed.

Definition SOne : object Setoids := [setoid: unit].

Lemma id_unique {C : Category} {a : C} (f : a ⟶ a) :
  (∀ {b} {g : a ⟶ b}, g ∘ f == g) /\ (∀ {b} {g : b ⟶ a}, f ∘ g == g) → f == identity.
Proof.
  intros.
  destruct H.

  refine
    (`begin
      f
     ↑⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      f ∘ identity
     =⟨ H0 _ identity ⟩
      identity
     `end).
Qed.
