Require Import Morphisms Setoid.
Require Import Utf8.

Require Program.Basics.
Module Func := Basics.

Require SetoidClass.
Module SC := SetoidClass.

Require Export CatQ.Setoids.

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
        compose ((compose (h , g)) , f) == compose (h , (compose (g , f)));
    left_identity:
      forall a b (f: morphism a b), compose (identity , f) == f;
    right_identity:
      forall a b (f: morphism a b), compose (f , identity) == f;
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

Definition comp (C : Category) : forall {a b c : C}, hom b c → hom a b → hom a c :=
  fun _ _ _ g f => compose (g , f).

Notation "A ⟶ B" := (hom A B) (at level 60, right associativity).
Notation "g ∘ f" := (comp g f) (at level 30).

Instance comp_proper {C : Category} {a b c : C} :
  Proper (@equality (morphism b c) ==> @equality (morphism a b) ==> @equality (morphism a c)) (fun g f => g ∘ f).
Proof.
  unfold comp, Proper, respectful.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Notation "`begin p" := p (at level 20, right associativity).
Notation "a =⟨ p 'at' C ⟩ pr" := (@Equivalence_Transitive (@morphism C _ _) _ _ a _ _ p pr) (at level 30, right associativity).
Notation "a =⟨ p ⟩ pr" := (@Equivalence_Transitive _ _ _ a _ _ p pr) (at level 30, right associativity).
Notation "a ↓⟨ p ⟩ pr" := (a =⟨ p ⟩ pr) (at level 30, right associativity).
Notation "a ↑⟨ p ⟩ pr" := (@Equivalence_Transitive _ _ _ a _ _ (@Equivalence_Symmetric p) pr) (at level 30, right associativity).
Notation "a `end" := (@Equivalence_Reflexive _ _ _ a) (at level 30).

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
      morphism := fun X Y =>
        {|
          carrier := @cat_hom ctype X Y;
          equality := @cat_hom_equal ctype _ _;
        |};
      identity := @cat_identity ctype;
      compose := fun a b c =>
        {|
          mapping := fun ps => @cat_comp ctype _ _ _ (fst ps) (snd ps);
        |};
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
      cat_comp := fun _ _ _ g f => @compose C _ _ _ (g,f);
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

(* Nat *)
Class Is_Nat
      {C D : Category} (F G : Functor C D)
      (component : forall a, morphism (F a) (G a)) :=
  {
    naturality : forall {a b} {f : a ⟶ b},
                   fmap G f ∘ component a == component b ∘ fmap F f;
  }.

Structure Nat {C D : Category} (F G : Functor C D) :=
  {
    component :> forall a, morphism (F a) (G a);
    is_nat :> Is_Nat component;
  }.
Existing Instance is_nat.

Definition naturality_of {C D} {F G : Functor C D} (α : Nat F G) :
  forall {a b} {f : a ⟶ b},
    fmap G f ∘ α a == α b ∘ fmap F f
  := @naturality C D F G (component α) (is_nat α).

Program Definition idNat {C D : Category} (F : Functor C D) : Nat F F :=
  {|
    component := fun a => @identity D (fobj F a);
  |}.
Next Obligation.
  apply Build_Is_Nat.
  intros.
  setoid_rewrite (@right_identity D).
  setoid_rewrite (@left_identity D).
  - reflexivity.
  - destruct D. simpl. auto.
  - destruct D. simpl. auto.
Defined.

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

Program Definition compNat {C D : Category} {F G H : Functor C D} (β : Nat G H) (α : Nat F G) : Nat F H :=
  {|
    component := fun a => component β a ∘ component α a;
  |}.
Next Obligation.
  apply Build_Is_Nat.
  intros.
  exact
    (`begin
      fmap H f ∘ (β a ∘ α a)
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (fmap H f ∘ β a) ∘ α a
     =⟨ ltac: (rewrite (naturality_of β); reflexivity) ⟩
      (β b ∘ fmap G f) ∘ α a
     =⟨ ltac: (rewrite assoc_of; reflexivity) ⟩
      β b ∘ (fmap G f ∘ α a)
     =⟨ ltac: (rewrite (naturality_of α); reflexivity) ⟩
      β b ∘ (α b ∘ fmap F f)
     =⟨ ltac: (rewrite <- assoc_of; reflexivity) ⟩
      (β b ∘ α b) ∘ fmap F f
     `end).
Defined.

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
    
  
