Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Program Definition One : Category :=
  Build_Category_from_Type
    {|
      cat_object := unit;
      cat_hom := fun _ _ => unit;
      cat_hom_equal := fun _ _ _ _ => True;
      cat_identity := fun _ => tt;
      cat_comp := fun _ _ _ _ _ => tt;
    |}.
Next Obligation.
  constructor.
  - auto.
  - auto.
  - auto.
Defined.
Next Obligation.
  constructor.
Defined.

