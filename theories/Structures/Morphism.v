Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Setoids Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Notation "A ⇋ B" := (prod (A → B) (B → A)) (at level 30).

Definition unique_hom {C : Category} {a b : C} (P : hom a b → Prop) (f : hom a b)
  := P f /\ forall (g : hom a b), P g → f == g.

Notation "∃ ! f .. g 'from' a 'to' b 'in' C , p" :=
  (sig (unique_hom (C:=C) (a:=a) (b:=b) (fun f => .. (sig (unique_hom (C:=C) (a:=a) (b:=b) (fun g => p))) ..)))
    (at level 200, f binder, right associativity,
     format "'[' ∃ ! '/ ' f .. g 'from' a 'to' b 'in' C , '/ ' p ']'").
Notation "∃ ! f .. g 'in' C , p" :=
  (sig (unique_hom (C:=C) (fun f => .. (sig (unique_hom (C:=C) (fun g => p))) ..)))
    (at level 200, f binder, right associativity,
     format "'[' ∃ ! '/ ' f .. g 'in' C , '/ ' p ']'").

Notation "⟨exist: f ⟩" := (proj1_sig f).

Lemma UMP_unique
      {C : Category} {a b : C} {P : hom a b → Prop} {p : ∃! (f : a ⟶ b) in C, P f} : forall f, P f → f == ⟨exist: p⟩.
Proof.
  intros.
  destruct p.
  simpl.
  destruct u.
  symmetry.
  apply (H1 f H).
Defined.

Class Is_isomorphic {C : Category} (x y : C)
      (iso_right : x ⟶ y) (iso_left: y ⟶ x) :=
  {
    iso_on_left : iso_left ∘ iso_right == identity;
    iso_on_right : iso_right ∘ iso_left == identity;
  }.

Structure isomorphic {C : Category} (x y : C) :=
  {
    iso_right : hom x y;
    iso_left : hom y x;
    is_isomorphic :> Is_isomorphic iso_right iso_left;
  }.
Existing Instance is_isomorphic.

Notation "[iso: f 'with' g 'as' A 'to' B ]" := (@Build_isomorphic _ A B f g _).
Notation "[iso: f 'with' g ]" := [iso: f with g as _ to _].

Lemma setiso_left_at {x y : Setoids} (iso: isomorphic x y) :
  forall u, iso_left iso (iso_right iso u) == u.
Proof.
  intros.
  apply (mapoid_apply u iso_on_left).
Qed.

Lemma setiso_right_at {x y : Setoids} (iso: isomorphic x y) :
  forall u, iso_right iso (iso_left iso u) == u.
Proof.
  intros.
  apply (mapoid_apply u iso_on_right).
Qed.

Notation "A ≃ B 'in' C" := (@isomorphic C A B) (at level 60, B at next level).
Infix "≃" := isomorphic (at level 60, only parsing).

Definition invertible {C : Category} {x y : C} (f : x ⟶ y) : Type
  := { g : y ⟶ x | f ∘ g == identity /\ g ∘ f == identity }.

Program Definition invertible_to_iso {C : Category} {x y : C} {f : x ⟶ y} : invertible f → x ≃ y in C
  := fun inv => [iso: f with proj1_sig inv ].
Next Obligation.
  destruct inv.
  destruct a.
  simpl.
  constructor.
  - assumption.
  - assumption.
Defined.
  
Definition is_invertible {C : Category} {x y : C} (f : x ⟶ y) : Prop
  := exists (g : y ⟶ x), f ∘ g == identity /\ g ∘ f == identity.

Definition iso_to_invertible {C : Category} {x y : C} : x ≃ y in C → ∃ (f : x ⟶ y), is_invertible f.
  intros.
  destruct X as [s t prop].
  exists s.
  unfold is_invertible.
  exists t.
  destruct prop as [prop1 prop2].
  split.
  - assumption.
  - assumption.
Defined.

Notation "f ⁻¹" := (proj1_sig (f : invertible _)) (at level 100).


