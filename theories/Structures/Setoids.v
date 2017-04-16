Require Import Morphisms Setoid.
Require Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(* Setoid *)

Structure Setoid :=
  {
    carrier :> Type;
    equality : carrier → carrier → Prop;
    is_setoid :> Equivalence equality;
  }.
Existing Instance is_setoid.

Notation "f == g 'of' X" := (@equality X f g) (at level 70, g at next level).
Infix "==" := equality (at level 70, only parsing).
Notation "[setoid: A 'with' eql 'by' prf ]" := (@Build_Setoid A eql prf).
Notation "[setoid: A 'with' eql ]" := [setoid: A with eql by _].
Notation "[setoid: A ]" := [setoid: A with eq].

Structure Mapoid (S S' : Setoid) :=
  {
    mapping :> S → S';
    is_mapoid :> Proper ((fun x y => equality x y) ==> (fun x y => equality x y)) mapping;
  }.
Existing Instance is_mapoid.

Notation "S -⇒ S'" := (Mapoid S S') (at level 60, right associativity).
Notation "[mapoid: f 'as' S 'to' S' 'by' prf ]" := (@Build_Mapoid S S' f prf).
Notation "[mapoid: f 'as' S 'to' S' ]" := [mapoid: f as S to S' by _ ].
Notation "[mapoid: f ]" := [mapoid: f as _ to _ ].
Notation "[mapoid: f 'by' prf ]" := [mapoid: f as _ to _ by prf ].

Program Definition idMapoid (S : Setoid) : S -⇒ S := [mapoid: fun x => x ].
Next Obligation.
  solve_proper.
Defined.

Program Definition Mapoid_space (S S' : Setoid) : Setoid :=
  [setoid: Mapoid S S' with (fun f g => forall (x : S), f x == g x) ].
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive.
    intros. reflexivity.
  - unfold Symmetric.
    intros. symmetry. apply H.
  - unfold Transitive.
    intros. rewrite H, H0. reflexivity.
Defined.

Program Definition Setoid_product (S S' : Setoid) : Setoid :=
  [setoid: S * S' with (fun x y => fst x == fst y /\ snd x == snd y)].
Next Obligation.
  apply Build_Equivalence.
  - unfold Reflexive.
    intros.
    split. reflexivity. reflexivity.
  - unfold Symmetric.
    intros. destruct H.
    rewrite H, H0.
    split. reflexivity. reflexivity.
  - unfold Transitive.
    intros.
    destruct H, H0.
    rewrite H, H1, H0, H2.
    split. reflexivity. reflexivity.
Defined.

Notation "S ** S'" := (Setoid_product S S') (at level 40).

Definition Spair (S S' : Setoid) : S → S' → S ** S' := pair.

Notation "(| x , y , .. , z |)" := (Spair .. (Spair x y) .. z).

Instance Spair_proper (S S' : Setoid) :
  Proper (@equality S ==> @equality S' ==> @equality (S ** S')) (fun x y => Spair x y).
Proof.
  unfold Proper, respectful, Setoid_product. simpl.
  intros.
  split.
  exact H. exact H0.
Qed.

(* Mapoid morphisms *)
Definition surj {S S'} (f : Mapoid S S') : Prop :=
  forall (s' : S'), exists s, f s == s'.

Definition inj {S S'} (f : Mapoid S S') : Prop :=
  forall (s₁ s₂ : S), f s₁ == f s₂ → s₁ == s₂.

(* Reasoning *)
Notation "`begin p" := p (at level 20, right associativity).
Notation "a =⟨ p ⟩ pr" := (@Equivalence_Transitive _ _ _ a _ _ p pr) (at level 30, right associativity).
Notation "a ↓⟨ p ⟩ pr" := (a =⟨ p ⟩ pr) (at level 30, right associativity).
Notation "a ↑⟨ p ⟩ pr" := (@Equivalence_Transitive _ _ _ a _ _ (@Equivalence_Symmetric p) pr) (at level 30, right associativity).
Notation "a `end" := (@Equivalence_Reflexive _ _ _ a) (at level 30).

