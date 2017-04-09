Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Definition unique_hom {C : Category} {a b : C} (P : hom a b → Prop) (f : hom a b)
  := P f /\ forall (g : hom a b), P g → f == g.

Notation "∃ ! f .. g 'from' a 'to' b 'in' C , p" :=
  (sig (unique_hom (C:=C) (a:=a) (b:=b) (fun f => .. (sig (unique_hom (C:=C) (a:=a) (b:=b) (fun g => p))) ..)))
    (at level 200, f binder, right associativity,
     format "'[' ∃ ! '/ ' f .. g 'from' a 'to' b '/ ' 'in' '/ ' C , '/ ' p ']'").
Notation "∃ ! f .. g 'in' C , p" :=
  (sig (unique_hom (C:=C) (fun f => .. (sig (unique_hom (C:=C) (fun g => p))) ..)))
    (at level 200, f binder, right associativity,
     format "'[' ∃ ! '/ ' f .. g '/ ' 'in' '/ ' C , '/ ' p ']'").

Structure isomorphic {C : Category} (x y : C) :=
  {
    iso_right : hom x y;
    iso_left : hom y x;
    iso_on_left : iso_left ∘ iso_right == identity;
    iso_on_right : iso_right ∘ iso_left == identity;
  }.

Notation "A ≃ B" := (isomorphic A B) (at level 60).
Notation "A ≃ B 'at' C" := (@isomorphic C A B) (at level 50).

Definition sig_isomorphism {C : Category} (x y : C) : Type
  := { fg: (x ⟶ y) * (y ⟶ x) | let (f,g) := fg in f ∘ g == identity /\ g ∘ f == identity }.

Definition sig_iso {C : Category} {x y : C} (f : x ⟶ y) : Type
  := { g : y ⟶ x | f ∘ g == identity /\ g ∘ f == identity }.

Definition iso_inv {C : Category} {x y : C} {f : x ⟶ y} : sig_iso f → (y ⟶ x) := fun sf => proj1_sig sf.

Notation "f ⁻¹" := (iso_inv f) (at level 30).

