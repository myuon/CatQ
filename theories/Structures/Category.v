Require Import Morphisms Setoid Vectors.Fin Classical.
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
      (identity: forall {x}, carrier (morphism x x))
      (compose: forall {a b c}, morphism b c ** morphism a b -⇒ morphism a c) :=
  {
    associativity:
      forall a b c d (f: morphism a b) (g: morphism b c) (h: morphism c d),
        compose (| compose (| h , g |) , f |) == compose (| h , compose (| g , f |) |);
    left_identity:
      forall a b (f: morphism a b), compose (| identity , f |) == f;
    right_identity:
      forall a b (f: morphism a b), compose (| f , identity |) == f;
  }.

Structure Category :=
  {
    object :> Type;
    morphism : object → object → Setoid;
    identity : forall {x}, carrier (morphism x x);
    compose : forall {a b c}, morphism b c ** morphism a b -⇒ morphism a c;
    is_category :> Is_Category (@identity) (@compose);
  }.
Existing Instance is_category.

Instance compose_proper (C : Category) :
  forall a b c, Proper ((@equality _) ==> (@equality _)) (@compose C a b c).
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

Definition comp (C : Category) : forall {a b c : C}, hom b c → hom a b → hom a c :=
  fun _ _ _ g f => compose (| g , f |).

Notation "A ⟶ B 'in' C" := (@hom C A B) (at level 60, B at next level, right associativity).
Infix "⟶" := hom (at level 60, only parsing).
Notation "g ∘ f" := (comp g f) (at level 30).
Notation "g ∘{ C } f" := (@comp C _ _ _ g f) (at level 30).

Instance comp_proper {C : Category} {a b c : C} :
  Proper (@equality (morphism b c) ==> @equality (morphism a b) ==> @equality (morphism a c)) (fun g f => g ∘ f).
Proof.
  unfold comp, Proper, respectful.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Notation "a =⟨ p 'at' C ⟩ pr" := (@Equivalence_Transitive (@morphism C _ _) _ _ a _ _ p pr) (at level 30, right associativity).

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

Inductive arrow {C : Category} : Type :=
| an_arrow: forall {a b : C} (f : a ⟶ b), arrow.

Notation "[arr: f ]" := (an_arrow f).

Definition domarr {C : Category} : @arrow C → C :=
  fun arr =>
    match arr with
      | (@an_arrow _ a _ _) => a
    end.

Definition codarr {C : Category} : @arrow C → C :=
  fun arr =>
    match arr with
      | (@an_arrow _ _ b _) => b
    end.

Definition from_arrow {C} (f : @arrow C) : domarr f ⟶ codarr f :=
  match f with
    | (@an_arrow _ _ _ f) => f
  end.

Axiom arr_unique : forall {C : Category} {a b : C} {f g : a ⟶ b}, [arr: f] = [arr: g] → f = g.

Inductive Heq_hom {C : Category} : @arrow C → @arrow C → Prop :=
| mk_Heq_hom : forall {a b} {f g : a ⟶ b}, f == g → Heq_hom (an_arrow f) (an_arrow g).

Notation "f ≈ g 'in' C" := (@Heq_hom C f g) (at level 70, g at next level).
Infix "≈" := Heq_hom (at level 70, only parsing).

Axiom Heq_eq : forall {C} (f g : @arrow C), f ≈ g →
      { fg : (domarr f ⟶ codarr f) * (domarr f ⟶ codarr f)
      | let '(f',g') := fg in
        [arr: f'] = f /\ [arr: g'] = g /\ domarr f = domarr g /\ codarr f = codarr g /\ f' == g'}.

Instance arr_proper {C a b} : Proper (@equality _ ==> @Heq_hom C) (fun (f : a ⟶ b) => [arr: f]).
Proof.
  unfold Proper, respectful.
  intros.
  constructor.
  exact H.
Qed.

Instance Heq_hom_equiv {C : Category} : Equivalence (fun f g => f ≈ g in C).
Proof.
  constructor.
  - unfold Reflexive.
    intros.
    destruct x.
    constructor.
    reflexivity.
  - unfold Symmetric.
    intros.
    destruct H.
    symmetry in H.
    constructor.
    exact H.
  - unfold Transitive.
    intros.
    destruct (Heq_eq H) as [(f,g)].
    destruct y0.
    destruct H2.
    destruct H3.
    destruct H4.

    generalize (Heq_eq H0).
    rewrite <- H1.
    rewrite <- H2.
    simpl.
    intro.
    destruct X as [(g',h)].

    destruct y0.
    destruct H7.
    destruct H8.
    destruct H9.

    assert (H11 := arr_unique H6).
    rewrite H11 in H10.

    assert (f == h).
    { rewrite H5, H10; reflexivity. }

    rewrite <- H7.
    constructor.
    exact H12.
Qed.

Instance eq_hom_equiv {C : Category} {a b : C} : Equivalence (fun (f : hom a b) g => f == g in C).
Proof.
  constructor.
  - unfold Reflexive.
    intros.
    reflexivity.
  - unfold Symmetric.
    intros.
    symmetry.
    exact H.
  - unfold Transitive.
    intros.
    rewrite H.
    exact H0.
Qed.

Structure Category_Type :=
  {
    cat_object : Type;
    cat_hom : cat_object → cat_object → Type;
    cat_identity : forall {x}, cat_hom x x;
    cat_comp : forall {a b c}, cat_hom b c → cat_hom a b → cat_hom a c;

    cat_hom_equal : forall {a b}, cat_hom a b → cat_hom a b → Prop;
    cat_hom_equal_equiv : forall {a b}, Equivalence (@cat_hom_equal a b);
    cat_comp_proper : forall {a b c}, Proper (cat_hom_equal ==> cat_hom_equal ==> cat_hom_equal) (@cat_comp a b c);

    cat_associativity : forall a b c d (f : cat_hom a b) (g : cat_hom b c) (h : cat_hom c d),
                          cat_hom_equal (cat_comp (cat_comp h g) f) (cat_comp h (cat_comp g f));
    cat_left_identity : forall a b (f : cat_hom a b),
                          cat_hom_equal (cat_comp cat_identity f) f;
    cat_right_identity : forall a b (f : cat_hom a b),
                          cat_hom_equal (cat_comp f cat_identity) f;
  }.

Program Definition Build_Category_from_Type : Category_Type → Category :=
  fun ctype =>
    {|
      object := cat_object ctype;
      morphism := fun X Y => [setoid: (@cat_hom ctype X Y) with (@cat_hom_equal ctype _ _)];
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
      cat_comp := fun _ _ _ g f => @compose C _ _ _ (| g , f |);
    |}.
Next Obligation.
  apply associativity.
Defined.
Next Obligation.
  apply left_identity.
Defined.
Next Obligation.
  apply right_identity.
Defined.

(* opposite *)
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
  unfold Proper, respectful, Func.flip.
  intros.
  rewrite H, H0.
  reflexivity.
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
      cat_identity := fun _ => {| mapping := fun x => x |};
      cat_comp := fun _ _ _ g f => {| mapping := fun x => g (f x) |};
    |}.
Next Obligation.
  unfold Proper, respectful.
  intros. exact H0.
Defined.
Next Obligation.
  unfold Proper, respectful.
  intros.
  rewrite H2.
  reflexivity.
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

Lemma hom_refl : forall {C : Category} {a b : C} {f : a ⟶ b}, f == f.
Proof.
  reflexivity.
Qed.  
