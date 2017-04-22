Require Import Morphisms Setoid ProofIrrelevance.
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

(* set with hetero equality (2-ary) *)
Class HEquivalence {A} (P : A → A → Type) (heq : forall {a b c d}, P a b → P c d → Prop) :=
  {
    hrefl : forall {a b} {x : P a b}, heq x x;
    hsym : forall {a b c d} {x : P a b} {y : P c d}, heq x y → heq y x;
    htrans : forall {a b c d e f} {x : P a b} {y : P c d} {z : P e f}, heq x y → heq y z → heq x z;
  }.

Structure HSetoid {A} (P : A → A → Type) :=
  {
    hequality : forall {a b c d}, P a b → P c d → Prop;
    is_hsetoid :> HEquivalence (@hequality);
  }.
Existing Instance is_hsetoid.

Notation "f ≈ g 'of' X" := (@hequality (X : HSetoid _) _ _ _ _ _ _ f g) (at level 70, g at next level).
Notation "[hsetoid: heq 'of' P 'by' prf ]" := (@Build_HSetoid _ P heq prf).
Notation "[hsetoid: heq 'of' P ]" := [hsetoid: heq of P by _].
Notation "[hsetoid: heq ]" := [hsetoid: heq of _].

Inductive heq_extending {A} {P : A → A → Setoid} {a b} (f : P a b) : forall {c d}, P c d → Prop :=
| mk_heq_extending : forall {g : P a b}, f == g of P a b → heq_extending f g.

Definition extend {A P} {a b c d : A} (ac: a = c) (bd: b = d) : P a b → P c d
  := fun f => eq_rect a (λ k, P k d) (eq_rect b (λ k, P a k) f d bd) c ac.

Lemma extend_refl {A} {P : A → A → Setoid} {a b : A} {f : P a b} : @extend A P a b a b eq_refl eq_refl f = f.
Proof.
  unfold extend.
  simpl.
  reflexivity.
Qed.

Axiom heq_extending_eq : forall {A} {P : A → A → Setoid} {a b c d : A} (f : P a b) (g : P c d),
    heq_extending f g → {eq : a = c /\ b = d | extend (P:=P) (proj1 eq) (proj2 eq) f == g}.

Program Definition HSetoid_on_setoid {A} (P : A → A → Setoid) : @HSetoid A P :=
  [hsetoid: fun a b c d x y => @heq_extending A P a b x c d y of P].
Next Obligation.
  constructor.
  - intros.
    constructor.
    reflexivity.
  - intros.
    destruct H.
    constructor.
    symmetry.
    apply H.
  - intros.
    destruct H, H0.
    constructor.
    rewrite H.
    apply H0.
Defined.

Lemma heqex_extend_eq {A} (P : A → A → Setoid) {a b : A} : forall {x y}, @equality (P a b) x y <-> heq_extending (P:=P) x y.
Proof.
  intros.
  constructor.
  - intro.
    constructor.
    exact H.
  - intro.
    destruct (heq_extending_eq H).
    destruct x0.
    rewrite <- e.

    assert (proj1 (conj e0 e1) = eq_refl).
    apply proof_irrelevance.
    assert (proj2 (conj e0 e1) = eq_refl).
    apply proof_irrelevance.
    rewrite H0, H1.
    unfold extend.
    simpl.
    reflexivity.
Defined.

Definition heq_on {A P} (S : @HSetoid A P) : forall {a b}, P a b → P a b → Prop
  := fun a b x y => hequality S x y.

Instance heq_extend_eq {A P} (S : @HSetoid A P) {a b} : Equivalence (heq_on S (a:=a) (b:=b)).
Proof.
  constructor.
  - unfold Reflexive, heq_on.
    intros.
    apply hrefl.
  - unfold Symmetric, heq_on.
    intros.
    apply (hsym H).
  - unfold Transitive, heq_on.
    intros.
    apply (htrans H H0).
Qed.

Definition Setoid_from_H {A P} (S : @HSetoid A P) {a b} : Setoid :=
  [setoid: P a b with heq_on S by heq_extend_eq S].

(* Reasoning *)
Definition Rtrans {A : Setoid} (a : A) {b c} (pr : b == c of A) (p : a == b of A) : a == c of A.
  rewrite p.
  exact pr.
Defined.

Definition Rtrans_sym {A : Setoid} (a : A) {b c} (pr : b == c of A) (p : b == a of A) : a == c of A.
  rewrite <- p.
  exact pr.
Defined.

Notation "`begin p" := p (at level 20, right associativity).
Notation "a =⟨ p ⟩ pr" := (@Rtrans _ a _ _ pr p) (at level 30, right associativity).
Notation "a ↓⟨ p ⟩ pr" := (a =⟨ p ⟩ pr) (at level 30, right associativity).
Notation "a ↑⟨ p ⟩ pr" := (@Rtrans_sym _ a _ _ pr p) (at level 30, right associativity).
Notation "a `end" := (@Equivalence_Reflexive _ _ _ a) (at level 30).
