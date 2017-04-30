Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(*
Lemma eqn_sym_inv_r {C D} {F F' : Functor C D} (eq : F ==f F') : proj1_sig (eqf_to_eqn eq) ∘n proj1_sig (eqf_to_eqn (symmetry eq)) == idNat in [D,D].
 *)

