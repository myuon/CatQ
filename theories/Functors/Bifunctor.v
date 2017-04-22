Require Import Morphisms Setoid.
Require Import Utf8.

Add LoadPath "../../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Definition Bifunctor (C D E : Category) := Functor (Product C D) E.

Program Definition homFunctor {C : Category} : Bifunctor (opposite C) C Setoids :=
  [fmap: fun a b ab => [mapoid: fun f => snd ab ∘ f ∘ fst ab]
   with fun a => @morphism C (fst a) (snd a) as (opposite C) × C to Setoids].
Next Obligation.
  simpl.
  unfold Proper, respectful.
  intros.
  destruct ab.
  simpl.
  simpl in c, c0.
  unfold Func.flip in c.
  rewrite H.
  reflexivity.
Defined.
Next Obligation.
  unfold Proper, respectful, Func.flip.
  simpl.
  intros.
  destruct x, y.
  destruct H.
  simpl in H, H0.
  simpl.
  rewrite H, H0.
  reflexivity.
Defined.
Next Obligation.
  rewrite left_id_of.
  rewrite right_id_of.
  reflexivity.
Defined.
Next Obligation.
  repeat rewrite assoc_of.
  reflexivity.
Defined.

Definition bimap {C D E} (G : Bifunctor C D E) {a b} (f : fst a ⟶ fst b) (g : snd a ⟶ snd b) : G a ⟶ G b
  := fmap G (Spair f g).

Instance bimap_proper {C D E} {G : Bifunctor C D E} {a b} :
  Proper (@equality _ ==> @equality _ ==> @equality _) (fun f g => bimap G (a:=a) (b:=b) f g).
Proof.
  unfold bimap.
  unfold Proper, respectful.
  intros.
  apply fmap_proper.
  simpl.
  auto.
Qed.

Lemma bimap_identity {C D E} (G : Bifunctor C D E) {a} : bimap G (a:=a) identity identity == identity.
Proof.
  unfold bimap.
  rewrite fmap_identity.
  reflexivity.
Qed.

Lemma bimap_compose {C D E} (G : Bifunctor C D E) {a b c}
      (f : fst a ⟶ fst b) (f' : fst b ⟶ fst c) (g : snd a ⟶ snd b) (g' : snd b ⟶ snd c) :
  bimap G (f' ∘ f) (g' ∘ g) == bimap G f' g' ∘ bimap G f g.
Proof.
  unfold bimap.
  rewrite <- fmap_compose.
  reflexivity.
Qed.

Program Definition Bifunctor_at_L {C D E} (G : Bifunctor C D E) (c : C) : Functor D E
  := [fmap: fun a b f => bimap G (a:=(c,a)) (b:=(c,b)) identity f with fun d => G (c,d) ].
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  apply bimap_identity.
Defined.
Next Obligation.
  rewrite <- bimap_compose.
  rewrite right_id_of.
  reflexivity.
Defined.

Notation "F [ a ,-]" := (Bifunctor_at_L F a) (at level 0).

Program Definition Bifunctor_at_R {C D E} (G : Bifunctor C D E) (d : D) : Functor C E
  := [fmap: fun a b f => bimap G (a:=(a,d)) (b:=(b,d)) f identity with fun c => G (c,d) ].
Next Obligation.
  solve_proper.
Defined.
Next Obligation.
  apply bimap_identity.
Defined.
Next Obligation.
  rewrite <- bimap_compose.
  rewrite right_id_of.
  reflexivity.
Defined.

Notation "F [-, a ]" := (Bifunctor_at_R F a) (at level 0).

Program Definition Bifunctor_apply_L {C D E} (G : Bifunctor C D E) {c c'} (k : c ⟶ c' in C) : Nat G[c,-] G[c',-]
  := [Nat: fun a => bimap G (a:=(c,a)) (b:=(c',a)) k identity ].
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap G[c',-] f ∘ bimap G (a:=(c,a)) (b:=(c',a)) k identity
     =⟨ hom_refl ⟩
      bimap G (a:=(c',a)) (b:=(c',b)) identity f ∘ bimap G (a:=(c,a)) (b:=(c',a)) k identity
     =⟨ ltac: (rewrite <- bimap_compose; reflexivity) ⟩
      bimap G (a:=(c,a)) (b:=(c',b)) (identity ∘ k) (f ∘ identity)
     =⟨ ltac: (rewrite right_id_of, left_id_of; reflexivity) ⟩
      bimap G (a:=(c,a)) (b:=(c',b)) k f
     ↑⟨ ltac: (rewrite right_id_of, left_id_of; reflexivity) ⟩
      bimap G (a:=(c,a)) (b:=(c',b)) (k ∘ identity) (identity ∘ f)
     =⟨ ltac: (rewrite <- bimap_compose; reflexivity) ⟩
      bimap G (a:=(c,b)) (b:=(c',b)) k identity ∘ bimap G (a:=(c,a)) (b:=(c,b)) identity f
     =⟨ hom_refl ⟩
      bimap G (a:=(c,b)) (b:=(c',b)) k identity ∘ fmap G[c,-] f
     `end).
Defined.

Notation "F [ f ,-]n" := (Bifunctor_apply_L F f) (at level 0).

Program Definition Bifunctor_apply_R {C D E} (G : Bifunctor C D E) {d d'} (k : d ⟶ d' in D) : Nat G[-,d] G[-,d']
  := [Nat: fun a => bimap G (a:=(a,d)) (b:=(a,d')) identity k].
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap G[-,d'] f ∘ bimap G (a:=(a,d)) (b:=(a,d')) identity k
     =⟨ hom_refl ⟩
      bimap (a:=(a,d')) (b:=(b,d')) G f identity ∘ bimap G (a:=(a,d)) (b:=(a,d')) identity k
     =⟨ ltac: (rewrite <- bimap_compose; reflexivity) ⟩
      bimap (a:=(a,d)) (b:=(b,d')) G (f ∘ identity) (identity ∘ k)
     =⟨ ltac: (rewrite right_id_of, left_id_of; reflexivity) ⟩
      bimap (a:=(a,d)) (b:=(b,d')) G f k
     ↑⟨ ltac: (rewrite right_id_of, left_id_of; reflexivity) ⟩
      bimap G (a:=(a,d)) (b:=(b,d')) (identity ∘ f) (k ∘ identity)
     =⟨ ltac: (rewrite <- bimap_compose; reflexivity) ⟩
      bimap G (a:=(b,d)) (b:=(b,d')) identity k ∘ bimap G (a:=(a,d)) (b:=(b,d)) f identity
     =⟨ hom_refl ⟩
      bimap G (a:=(b,d)) (b:=(b,d')) identity k ∘ fmap G[-,d] f
     `end).
Defined.

Notation "F [-, f ]n" := (Bifunctor_apply_R F f) (at level 0).

