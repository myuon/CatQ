Require Import Morphisms Setoid Coq.Vectors.Fin.
Require Import Utf8.

Add LoadPath "../theories" as CatQ.
From CatQ.Structures Require Import Structures.
From CatQ.Categories Require Import FunCat Concrete.
From CatQ.Functors Require Import Bifunctor Concrete.
Require Import CatQ.UniversalArrow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Structure Adjoint {C D} (F : Functor C D) (G : Functor D C) :=
  {
    adjunction : Nat (homFunctor ∘f ⟨ProductF: opf F , idFunctor⟩) (homFunctor ∘f ⟨ProductF: idFunctor , G⟩);
    is_adjoint : natiso adjunction;
  }.

Notation "[adjoint: F , G 'as' C 'to' D ]" := (@Adjoint C D F G) (at level 0, G at next level).
Notation "F ⊣ G" := [adjoint: F , G as _ to _] (at level 10).

Definition adj_iso {C D F G} (ψ: [adjoint: F,G as C to D]) : forall {c d}, morphism (F c) d ≃ morphism c (G d) in Setoids
  := fun c d => invertible_to_iso (is_adjoint ψ (c,d)).

Definition adj_r {C D F G} (ψ: [adjoint: F,G as C to D]) : forall {c d}, morphism (F c) d ⟶ morphism c (G d) in Setoids
  := fun c d => iso_right (adj_iso ψ (c:=c) (d:=d)).

Definition adj_l {C D F G} (ψ: [adjoint: F,G as C to D]) : forall {c d}, morphism c (G d) ⟶ morphism (F c) d in Setoids
  := fun c d => iso_left (adj_iso ψ (c:=c) (d:=d)).

Notation "[adj: f 'of' p ]" := (adj_r p f).
Notation "[adj: f ]" := [adj: f of _].
Notation "[adj⁻¹: f 'of' p ]" := (adj_l p f).
Notation "[adj⁻¹: f ]" := [adj⁻¹: f of _].

Lemma adj_isomorphic {C D F G} (ψ : [adjoint: F,G as C to D]) :
  forall {c d} (u : F c ⟶ d), [adj⁻¹: [adj: u of ψ] of ψ] == u.
Proof.
  intros.
  unfold adj_r, adj_l.
  rewrite setiso_left_at.
  reflexivity.
Qed.

Lemma adj_inv_isomorphic {C D F G} (ψ : [adjoint: F,G as C to D]) :
  forall {c d} (u : c ⟶ G d), [adj: [adj⁻¹: u of ψ] of ψ] == u.
Proof.
  intros.
  unfold adj_r, adj_l.
  rewrite setiso_right_at.
  reflexivity.
Qed.

Lemma adj_natural_L
      {C D F G} (ψ : [adjoint: F,G as C to D]) {c c' d} (f : c ⟶ c') (u : F c' ⟶ d) :
  [adj: u ∘ fmap F f of ψ] == [adj: u of ψ] ∘ f.
Proof.
  unfold adj_r.
  simpl.
  destruct (adjunction ψ).
  destruct is_nat.
  generalize (mapoid_apply u (naturality (c',d) (c,d) (f,identity))).
  simpl.
  intro.
  symmetry.

  refine
    (`begin
      component (c',d) u ∘ f
     =⟨ hom_refl ⟩
      component (c',d) u ∘ fmap idFunctor f
     =⟨ _ ⟩
      (identity ∘ component (c',d) u) ∘ fmap idFunctor f
     =⟨ _ ⟩
      (fmap G identity ∘ component (c',d) u) ∘ fmap idFunctor f
     =⟨ H ⟩
      component (c,d) ((fmap idFunctor identity ∘ u) ∘ fmap (opf F) f)
     =⟨ hom_refl ⟩
      component (c,d) ((identity ∘ u) ∘ fmap (opf F) f)
     =⟨ mapoid_cong (component (c,d)) _ ⟩
      component (c,d) (u ∘ fmap (opf F) f)
     =⟨ hom_refl ⟩
      component (c,d) (u ∘ fmap F f)
     `end).

  - unfold opf, op_trf; simpl.
    unfold fmap; simpl.
    unfold opop_invf; simpl.
    unfold fmap; simpl.
    unfold opposite_hom, opposite_hom_to.
    rewrite left_id_of.
    reflexivity.
  - rewrite left_id_of.
    rewrite fmap_identity.
    rewrite left_id_of.
    reflexivity.
  - rewrite left_id_of.
    reflexivity.
Qed.

Lemma adj_natural_R
      {C D F G} (ψ : [adjoint: F,G as C to D]) {c d d'} (g : d ⟶ d') (u : F c ⟶ d) :
  [adj: g ∘ u of ψ] == fmap G g ∘ [adj: u of ψ].
Proof.
  unfold adj_r.
  simpl.
  destruct (adjunction ψ).
  destruct is_nat.
  generalize (naturality (c,d) (c,d') (identity,g) u).
  simpl.
  intro.

  refine
    (`begin
      component (c,d') (g ∘ u)
     =⟨ _ ⟩
      component (c,d') ((g ∘ u) ∘ identity)
     =⟨ _ ⟩
      component (c,d') ((g ∘ u) ∘ fmap (opf F) identity)
     =⟨ _ ⟩
      component (c,d') ((fmap idFunctor g ∘ u) ∘ fmap (opf F) identity)
     ↑⟨ H ⟩
      (fmap G g ∘ component (c,d) u) ∘ fmap idFunctor identity
     =⟨ ltac: (rewrite fmap_identity; reflexivity) ⟩
      (fmap G g ∘ component (c,d) u) ∘ identity
     =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      fmap G g ∘ component (c,d) u
     `end).

  - apply mapoid_cong.
    unfold opf.
    unfold op_trf, opop_invf.
    simpl.
    unfold fmap; simpl.
    unfold fmap; simpl.
    unfold opposite_hom_to, opposite_hom.
    reflexivity.
  - apply mapoid_cong.
    unfold opf.
    unfold op_trf, opop_invf.
    simpl.
    unfold fmap; simpl.
    unfold fmap; simpl.
    unfold opposite_hom_to, opposite_hom.
    rewrite fmorphism_identity.
    reflexivity.
  - rewrite right_id_of.
    reflexivity.
Qed.

Lemma adj_inv_natural_L
      {C D F G} (ψ : [adjoint: F,G as C to D]) {c c' d} (f : c ⟶ c') (u : c' ⟶ G d) :
  [adj⁻¹: u of ψ] ∘ fmap F f == [adj⁻¹: u ∘ f of ψ].
Proof.
  refine
    (`begin
      [adj⁻¹: u of ψ] ∘ fmap F f
     ↑⟨ ltac: (rewrite (setiso_left_at (adj_iso ψ)); reflexivity) ⟩
      [adj⁻¹: [adj: [adj⁻¹: u of ψ] ∘ fmap F f]]
     =⟨ ltac: (rewrite (adj_natural_L ψ); reflexivity) ⟩
      [adj⁻¹: [adj: [adj⁻¹: u of ψ]] ∘ f]
     =⟨ ltac: (rewrite adj_inv_isomorphic; reflexivity) ⟩
      [adj⁻¹: u ∘ f of ψ]
      `end).
Qed.

Lemma adj_inv_natural_R
      {C D F G} (ψ : [adjoint: F,G as C to D]) {c d d'} (g : d ⟶ d') (u : c ⟶ G d) :
  [adj⁻¹: fmap G g ∘ u of ψ] == g ∘ [adj⁻¹: u of ψ].
Proof.
  refine
    (`begin
      [adj⁻¹: fmap G g ∘ u of ψ]
     ↑⟨ ltac: (rewrite (adj_inv_isomorphic ψ u); reflexivity) ⟩
      [adj⁻¹: fmap G g ∘ [adj: [adj⁻¹: u of ψ]]]
     =⟨ ltac: (rewrite <- (adj_natural_R ψ); reflexivity) ⟩
      [adj⁻¹: [adj: g ∘ [adj⁻¹: u of ψ]]]
     =⟨ ltac: (rewrite (adj_isomorphic ψ); reflexivity) ⟩
      g ∘ [adj⁻¹: u of ψ]
     `end).
Qed.

Lemma adj_comm {C D F G} (ψ : [adjoint: F , G as C to D]) {c c' d d'}
      {f : F c ⟶ d} {h : F c' ⟶ d'} {p : c ⟶ c'} {q : d ⟶ d'} :
  h ∘ fmap F p == q ∘ f → [adj: h of ψ] ∘ p == fmap G q ∘ [adj: f of ψ].
Proof.
  intro hyp.
  refine
    (`begin
      [adj:h] ∘ p
     =⟨ ltac: (rewrite <- (adj_natural_L ψ p h); reflexivity) ⟩
      [adj:h ∘ fmap F p]
     =⟨ ltac: (rewrite hyp; reflexivity) ⟩
      [adj:q ∘ f]
     =⟨ ltac: (rewrite (adj_natural_R ψ q f); reflexivity) ⟩
      fmap G q ∘ [adj:f]                  
     `end).
Qed.

Program Definition unit {C D F G} (ψ : [adjoint: F,G as C to D]) : idFunctor ⟶ (G ∘f F) in [C,C]
  := [Nat: fun c => [adj: @identity _ (F c) of ψ] ].
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap G (fmap F f) ∘ [adj: identity of ψ]
     ↑⟨ ltac: (rewrite (adj_natural_R ψ); reflexivity) ⟩
      [adj: fmap F f ∘ identity]
     =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      [adj: fmap F f]
     ↑⟨ ltac: (rewrite (@left_id_of D); reflexivity) ⟩
      [adj: identity ∘ fmap F f]
     =⟨ ltac: (rewrite (adj_natural_L ψ); reflexivity) ⟩
      [adj: identity of ψ] ∘ f
     =⟨ hom_refl ⟩
      [adj: identity of ψ] ∘ fmap idFunctor f
     =⟨ hom_refl ⟩
      (adjunction ψ (b,F b)) identity ∘ fmap idFunctor f
     `end).
Defined.

Program Definition unit_universality {C D F G} (ψ : [adjoint: F,G as C to D]) : forall c, UniversalArrow c G
  := fun c => [universal: F c with unit ψ c].
Next Obligation.
  exists [adj⁻¹: f of ψ].
  constructor.
  - refine
      (`begin
        fmap G [adj⁻¹: f] ∘ [adj: identity]
       =⟨ ltac: (rewrite <- (adj_natural_R ψ); reflexivity) ⟩
        [adj: [adj⁻¹: f] ∘ identity]
       =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
        [adj: [adj⁻¹: f]]
       =⟨ ltac: (rewrite (adj_inv_isomorphic ψ); reflexivity) ⟩
        f
        `end).
  - intros.
    refine
      (`begin
        [adj⁻¹: f]
       =⟨ ltac: (rewrite <- H; reflexivity) ⟩
        [adj⁻¹: fmap G g ∘ [adj: identity]]
       =⟨ ltac: (rewrite <- adj_natural_R; reflexivity) ⟩
        [adj⁻¹: [adj: g ∘ identity]]
       =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩ 
        [adj⁻¹: [adj: g]]
       =⟨ ltac: (rewrite (adj_isomorphic ψ); reflexivity) ⟩ 
        g
       `end).
Defined.

Program Definition counit {C D F G} (ψ : [adjoint: F,G as C to D]) : (F ∘f G) ⟶ idFunctor in [D,D]
  := [Nat: fun d => [adj⁻¹: @identity _ (G d) of ψ] ].
Next Obligation.
  constructor.
  intros.

  refine
    (`begin
      fmap idFunctor f ∘ [adj⁻¹: identity]
     =⟨ hom_refl ⟩
      f ∘ [adj⁻¹: identity]
     ↑⟨ ltac: (rewrite (adj_inv_natural_R ψ); reflexivity) ⟩
      [adj⁻¹: fmap G f ∘ identity]
     =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      [adj⁻¹: fmap G f]
     ↑⟨ ltac: (rewrite (@left_id_of C); reflexivity) ⟩
      [adj⁻¹: identity ∘ fmap G f]
     ↑⟨ ltac: (rewrite (adj_inv_natural_L ψ); reflexivity) ⟩
      [adj⁻¹: identity] ∘ fmap F (fmap G f)
     =⟨ hom_refl ⟩
      [adj⁻¹: identity] ∘ fmap (F ∘f G) f
     `end).
Defined.

Proposition triangular_R {C D F G} (ψ : [adjoint: F,G as C to D]) : rightIdFunctor ∘n ((G f⋆ counit ψ) ∘n assocFunctor ∘n (unit ψ ⋆f G)) == @identity [D,C] G ∘n leftIdFunctor in [D,C].
Proof.
  simpl.
  intro.

  refine
    (`begin
      identity ∘ ((fmap G [adj⁻¹: identity] ∘ identity) ∘ [adj: identity])
     =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      identity ∘ (fmap G [adj⁻¹: identity] ∘ [adj: identity])
     =⟨ ltac: (rewrite <- (adj_natural_R ψ); reflexivity) ⟩
      identity ∘ [adj: [adj⁻¹: identity] ∘ identity]
     =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      identity ∘ [adj: [adj⁻¹: identity]]
     =⟨ ltac: (rewrite (adj_inv_isomorphic ψ (d:=A)); reflexivity) ⟩
      identity ∘ identity
     `end).
Defined.

Proposition triangular_L {C D F G} (ψ : [adjoint: F,G as C to D]) : leftIdFunctor ∘n ((counit ψ ⋆f F) ∘n assocInvFunctor ∘n (F f⋆ unit ψ)) == @identity [C,D] F ∘ rightIdFunctor in [C,D].
Proof.
  simpl.
  intro.

  refine
    (`begin
      identity ∘ (([adj⁻¹:identity] ∘ identity) ∘ fmap F [adj:identity])
     =⟨ ltac: (rewrite right_id_of; reflexivity) ⟩
      identity ∘ ([adj⁻¹: identity] ∘ fmap F [adj: identity])
     =⟨ ltac: (rewrite (adj_inv_natural_L ψ (d:=F A)); reflexivity) ⟩
      identity ∘ [adj⁻¹: identity ∘ [adj:identity] ]
     =⟨ ltac: (rewrite (@left_id_of C); reflexivity) ⟩
      identity ∘ [adj⁻¹: [adj:identity] ]
     =⟨ ltac: (rewrite (adj_isomorphic ψ (c:=A)); reflexivity) ⟩
      identity ∘ identity
     `end).
Defined.


(*
Section left_adjoint_from_unit_proof.
  Variable (C D : Category) (G : Functor D C).
  Variable (ηt : forall c, UniversalArrow_Type c G).

  Program Definition left_adj : Functor C D :=
    [fmap: fun c c' p => proj1_sig (ua_UMP (ηt c) (f:=ua_map (ηt c') ∘ p)) with fun c => ua_object (ηt c)].
  Next Obligation.
    unfold Proper, respectful; simpl.
    intros.
    destruct (ηt a) as [ηtobj ηtmap ηtprop].
    simpl.
    destruct (ηtprop (ua_object (ηt b)) (ua_map (ηt b) ∘ x)).
    simpl.
    destruct (ηtprop (ua_object (ηt b)) (ua_map (ηt b) ∘ y)).
    simpl.
    destruct u.
    destruct u0.
    rewrite (H1 x1).
    reflexivity.
    rewrite H2.
    rewrite H.
    reflexivity.
  Defined.
  Next Obligation.
    destruct (ηt a).
    simpl.
    destruct (ua_UMP ua_object).
    simpl.
    destruct u.
    apply (H0 identity).
    rewrite fmap_identity.
    rewrite right_id_of.
    rewrite left_id_of.
    reflexivity.
  Defined.
  Next Obligation.
  Admitted.

  Program Definition φ {c d} : (morphism (left_adj c) d) ≃ (morphism c (G d)) at Setoids :=
    {|
      iso_right := [mapoid: fun g => fmap G g ∘ ua_map (ηt c)];
    |}.
  Next Obligation.
    solve_proper.
  Defined.
  Next Obligation.
    
Lemma left_adjoint_from_unit {C D} {G : Functor D C} {η : forall c, UniversalArrow c G} : {F : Functor C D & F ⊣ G}.
Proof.
  refine (existT (fun F => F ⊣ G) [fmap: fun c c' p => proj1_sig (ua_UMP (Destruct_UniversalArrow_Type (η c)) (f:=ua_map (Destruct_UniversalArrow_Type (η c')) ∘ p)) with fun c => ua_object (Destruct_UniversalArrow_Type (η c))] _).
  {
    simpl.
    refine {| adjunction := _ |}.
    {
      intros.
      unfold fmap; simpl.
    }
  }

*)


