Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Lemma eqn_sym_inv_r {C D} {F F' : Functor C D} (eq : F ==f F') : proj1_sig (eqf_to_eqn eq) ∘n proj1_sig (eqf_to_eqn (symmetry eq)) == idNat F' in [C,D].
Proof.
  simpl.
  intro.
  unfold eq_to_hom.
  rewrite <- extend_compose_left, extend_eq.
  rewrite left_id_of.
  rewrite extend_trans.
  rewrite extend_eq.
  reflexivity.
Qed.

Lemma eqn_sym_inv_l {C D} {F F' : Functor C D} (eq : F ==f F') : proj1_sig (eqf_to_eqn (symmetry eq)) ∘n proj1_sig (eqf_to_eqn eq) == idNat F in [C,D].
Proof.
  simpl.
  intro.
  unfold eq_to_hom.
  rewrite <- extend_compose_left, extend_eq.
  rewrite left_id_of.
  rewrite extend_trans.
  rewrite extend_eq.
  reflexivity.
Qed.

Lemma eq_sym_of_eqf {C D} {F F' : Functor C D} (eq : F ==f F') {A} : (~ proj1_sig eq A) = proj1_sig (symmetry eq) A.
Proof.
  destruct eq.
  simpl.
  reflexivity.
Qed.

Lemma nat_extend {C D} {F G : Functor C D} {η : Nat F G} {a b} (p : a = b) :
  extend (fobj_eq p) (fobj_eq p) (η a) = η b.
Proof.
  destruct p.
  auto.
Qed.

Lemma fstar_distr {C D U} {S : Functor D U} {F G H : Functor C D} {α : Nat G H} {β : Nat F G} : S f⋆ (α ∘n β) == (S f⋆ α) ∘n (S f⋆ β) in [C,U].
Proof.
  simpl.
  intro.
  apply fmap_compose.
Qed.

Lemma fobj_eq_preserve_sym {C D} {F : Functor C D} {a b : C} (p : a = b) : (~ fobj_eq (F:=F) p) = fobj_eq (~ p).
Proof.
  destruct p.
  auto.
Qed.

