Require Import Morphisms Setoid ProofIrrelevance.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Setoids Category Functor Nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Notation "s ∙ t" := (eq_trans s t) (at level 40).
Notation "~ s" := (eq_sym s).

Section EqFunctor.
  Program Definition extend {C : Category} {a b c d : C} (ac: a = c) (bd: b = d) : morphism a b -⇒ morphism c d
    := [mapoid: fun f => eq_rect a (λ k, k ⟶ d in C) (eq_rect b (λ k, a ⟶ k in C) f d bd) c ac].
  Next Obligation.
    solve_proper.
  Defined.

  Lemma extend_eq {C : Category} {a b : C} (p: a = a) (q: b = b) {f : a ⟶ b} : extend p q f == f.
  Proof.
    unfold extend.
    simpl.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    reflexivity.
  Qed.
  
  Lemma extend_irrelevance {C : Category} {a b c d : C} (p p': a = c) (q q': b = d) {f : a ⟶ b} : extend p q f == extend p' q' f.
  Proof.
    destruct p.
    destruct q.
    rewrite extend_eq.
    rewrite extend_eq.
    reflexivity.
  Qed.

  Lemma extend_trans {C : Category} {a1 b1 a2 b2 a3 b3 : C} (p: a1 = a2) (p': a2 = a3) (q: b1 = b2) (q': b2 = b3) {f : a1 ⟶ b1} : extend p' q' (extend p q f) = extend (p ∙ p') (q ∙ q') f.
  Proof.
    unfold extend.
    simpl.
    destruct p, p', q, q'.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    rewrite <- eq_rect_eq.
    reflexivity.
  Qed.

  Lemma extend_compose_right {C : Category} {a1 b1 a2 b2 c : C} (p: a1 = a2) (q: b1 = b2) {f : a1 ⟶ b1} {g : b2 ⟶ c} : extend p eq_refl (g ∘ extend eq_refl q f) = g ∘ extend p q f.
  Proof.
    destruct p, q.
    simpl.
    reflexivity.
  Qed.

  Lemma extend_compose_left {C : Category} {a1 b1 a2 b2 c : C} (p: a1 = a2) (q: b1 = b2) {f : a1 ⟶ b1} {g : c ⟶ a2} : extend eq_refl q (extend p eq_refl f ∘ g) = extend p q f ∘ g.
  Proof.
    destruct p, q.
    simpl.
    reflexivity.
  Qed.

  Lemma extend_compose_factor {C : Category} {a' a b c c' : C} (p: a = a') (q: c = c') {f : a ⟶ b} {g : b ⟶ c} : extend p q (g ∘ f) = extend eq_refl q g ∘ extend p eq_refl f.
  Proof.
    destruct p, q.
    simpl.
    reflexivity.
  Qed.

  Lemma extend_id_flip_l {C : Category} {a b : C} (p: a = b) : extend eq_refl p identity == extend (~ p) eq_refl identity.
  Proof.
    destruct p.
    simpl.
    reflexivity.
  Qed.

  Lemma extend_id_flip_r {C : Category} {a b : C} (p: a = b) : extend p eq_refl identity == extend eq_refl (~ p) identity.
  Proof.
    destruct p.
    simpl.
    reflexivity.
  Qed.

  Lemma extend_compose_flip_l {C : Category} {a a' b b' c : C} (p: a = a') (q: b = b') {f : a ⟶ b} {g: b' ⟶ c}
    : g ∘ extend p q f == extend (~ q) eq_refl g ∘ extend p eq_refl f.
  Proof.
    destruct p, q.
    simpl.
    reflexivity.
  Qed.

  Lemma extend_compose_flip_r {C : Category} {a a' b b' c : C} (p: a = a') (q: b = b') {f : a ⟶ b} {g: c ⟶ a'}
    : extend p q f ∘ g == extend eq_refl q f ∘ extend eq_refl (~ p) g.
  Proof.
    destruct p, q.
    simpl.
    reflexivity.
  Qed.

  Definition fobj_eq {C D} {F : Functor C D} {a b} : a = b → F a = F b.
    intro.
    rewrite H.
    reflexivity.
  Defined.

  Lemma fmap_preserve_extend {C D : Category} (F : Functor C D) {a b c d : C} (p: a = c) (q: b = d) {f : a ⟶ b}
    : fmap F (extend p q f) == extend (fobj_eq p) (fobj_eq q) (fmap F f).
  Proof.
    destruct p.
    destruct q.
    rewrite extend_eq.
    rewrite extend_eq.
    reflexivity.
  Qed.

  Definition eqFunctor {C D} (F G : Functor C D) :=
    {eq: forall x, F x = G x | forall {a b} (f : a ⟶ b), extend (eq a) (eq b) (fmap F f) == fmap G f }.

  Lemma eqFunctor_obj {C D} {F F' : Functor C D} : eqFunctor F F' → forall a, F a = F' a.
  Proof.
    intros.
    destruct H.
    apply x.
  Qed.
End EqFunctor.

Instance eqFunctor_equiv {C D} : Equivalence (@eqFunctor C D).
Proof.
  constructor.
  - unfold Reflexive, eqFunctor.
    intros.
    exists (fun _ => eq_refl).
    intros.
    rewrite extend_eq.
    reflexivity.
  - unfold Symmetric.
    intros.
    unfold eqFunctor.
    destruct H.
    exists (fun t => eq_sym (x0 t)).
    intros.
    rewrite <- e.
    rewrite extend_trans.
    rewrite extend_eq.
    reflexivity.
  - unfold Transitive.
    intros.
    unfold eqFunctor.
    intros.
    destruct H0.
    destruct H.
    exists (fun t => eq_trans (x1 t) (x0 t)).
    intros.
    rewrite <- e.
    rewrite <- e0.
    rewrite extend_trans.
    reflexivity.
Defined.

Notation "F ==f G" := (eqFunctor F G) (at level 40).

Section Nat_Eqf.
  Definition nat_eqf {C D} (F G : Functor C D) :=
    {η : Nat F G | ∃ (eq : forall x, F x = G x), forall {a}, extend (eq a) eq_refl (η a) == identity}.
End Nat_Eqf.

Notation "F ==n G" := (nat_eqf F G) (at level 40).

Section Eqf_And_EqfNat.
  Definition eq_to_hom {C : Category} {a b : C} (p : a = b) : a ⟶ b := extend eq_refl p (@identity _ a).
  
  Program Definition nat_of_from_eqf {C D} (F G : Functor C D) : F ==f G → Nat F G
    := fun FG => [Nat: fun a => eq_to_hom (proj1_sig FG a)].
  Next Obligation.
    constructor.
    intros.
    destruct FG.
    simpl.
    unfold eq_to_hom.
    generalize (e a a identity); intro.
    rewrite fmap_identity in H.
    rewrite fmap_identity in H.
    generalize (e b b identity); intro.
    rewrite fmap_identity in H0.
    rewrite fmap_identity in H0.

    generalize (e a b f); intro.

    assert (extend (~ (x a)) (~ (x a)) identity == identity).
    {
      rewrite <- H.
      rewrite extend_trans.
      rewrite extend_eq.
      reflexivity.
    }

    refine
      (`begin
        fmap G f ∘ extend eq_refl (x a) identity
       =⟨ ltac: (rewrite extend_id_flip_l; reflexivity) ⟩
        fmap G f ∘ extend (~ x a) eq_refl identity
       ↑⟨ ltac: (rewrite extend_eq; reflexivity) ⟩
        extend eq_refl eq_refl (fmap G f) ∘ extend (~ x a) eq_refl identity
       =⟨ ltac: (rewrite extend_compose_factor; reflexivity) ⟩
        extend (~ x a) eq_refl (fmap G f ∘ identity)
       =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
        extend (~ x a) eq_refl (fmap G f)
       ↑⟨ ltac: (rewrite H1; reflexivity) ⟩
        extend (~ x a) eq_refl (extend (x a) (x b) (fmap F f))
       =⟨ ltac: (rewrite extend_trans; reflexivity) ⟩
        extend (x a ∙ ~ x a) (x b ∙ eq_refl) (fmap F f)
       =⟨ ltac: (rewrite eq_trans_sym_inv_r, eq_trans_refl_r; reflexivity) ⟩
        extend eq_refl (x b) (fmap F f)
       ↑⟨ ltac: (rewrite left_id_of; reflexivity) ⟩
        extend eq_refl (x b) (identity ∘ fmap F f)
       ↑⟨ ltac: (rewrite extend_eq; reflexivity) ⟩
        extend eq_refl (x b) (extend eq_refl eq_refl identity ∘ fmap F f)
       =⟨ ltac: (rewrite (extend_compose_left eq_refl (x b) (f:=identity) (g:=fmap F f)); reflexivity) ⟩
        extend eq_refl (x b) identity ∘ fmap F f
       `end).
  Defined.
    
  Program Definition eqf_to_eqn {C D} (F G : Functor C D) : F ==f G → F ==n G
    := fun FG => nat_of_from_eqf FG.
  Next Obligation.
    destruct FG.
    exists x.
    unfold eq_to_hom.
    simpl.
    intro.

    assert (extend (x a) (x a) identity = eq_rect (F a) (λ k : D, k ⟶ G a in D) (eq_rect (F a) (λ k : D, F a ⟶ k in D) identity (G a) (x a)) (G a) (x a)).
    reflexivity.

    rewrite <- H.
    apply id_unique.
    split.
    - intros.
      refine
        (`begin
          g ∘ extend (x a) (x a) identity
         =⟨ ltac: (rewrite <- extend_compose_right; reflexivity) ⟩
          extend (x a) eq_refl (g ∘ extend eq_refl (x a) identity)
         =⟨ ltac: (rewrite extend_id_flip_l; reflexivity) ⟩
          extend (x a) eq_refl (g ∘ extend (~ x a) eq_refl identity)
         =⟨ ltac: (rewrite extend_compose_factor; reflexivity) ⟩
          extend eq_refl eq_refl g ∘ extend (x a) eq_refl (extend (~ x a) eq_refl identity)
         =⟨ ltac: (rewrite extend_trans; reflexivity) ⟩
          extend eq_refl eq_refl g ∘ extend ((~ x a) ∙ x a) (eq_refl ∙ eq_refl) identity
         =⟨ ltac: (rewrite eq_trans_sym_inv_l, eq_trans_refl_l; reflexivity) ⟩
          extend eq_refl eq_refl g ∘ extend eq_refl eq_refl identity
         =⟨ ltac: (rewrite extend_eq, extend_eq; reflexivity) ⟩
          g ∘ identity
         =⟨ right_id_of ⟩
          g
         `end).
    - intros.
      refine
        (`begin
          extend (x a) (x a) identity ∘ g
         ↑⟨ ltac: (rewrite extend_compose_left; reflexivity) ⟩
          extend eq_refl (x a) (extend (x a) eq_refl identity ∘ g)
         =⟨ ltac: (rewrite extend_id_flip_r; reflexivity) ⟩
          extend eq_refl (x a) (extend eq_refl (~ x a) identity ∘ g)
         =⟨ ltac: (rewrite extend_compose_factor; reflexivity) ⟩
          extend eq_refl (x a) (extend eq_refl (~ x a) identity) ∘ extend eq_refl eq_refl g
         =⟨ ltac: (rewrite extend_trans; reflexivity) ⟩
          extend (eq_refl ∙ eq_refl) ((~ x a) ∙ x a) identity ∘ extend eq_refl eq_refl g
         =⟨ ltac: (rewrite eq_trans_sym_inv_l, eq_trans_refl_l; reflexivity) ⟩
          extend eq_refl eq_refl identity ∘ extend eq_refl eq_refl g
         =⟨ ltac: (rewrite extend_eq, extend_eq; reflexivity) ⟩
          identity ∘ g
         =⟨ left_id_of ⟩
          g
         `end).
  Defined.
End Eqf_And_EqfNat.

