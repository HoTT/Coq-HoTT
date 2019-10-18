(** This file develops [Isomorphic], [≅]. See ua_homomorphism.v for
    [IsHomomorphism] and [IsIsomorphism]. *)

Require Export HoTT.Classes.theory.ua_homomorphism.

Require Import
  HoTT.Basics.Overture
  HoTT.Basics.Trunc
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.Tactics.

(** Two algebras [A B : Algebra σ] are isomorphic if there is an
    isomorphism [∀ s, A s → B s]. *)

Record Isomorphic {σ : Signature} (A B : Algebra σ) := BuildIsomorphic
  { def_isomorphic : ∀ s, A s → B s
  ; is_homomorphism_isomorphic : IsHomomorphism def_isomorphic
  ; is_isomorphism_isomorphic : IsIsomorphism def_isomorphic }.

Arguments BuildIsomorphic {σ A B} def_isomorphic
            {is_homomorphism_isomorphic} {is_isomorphism_isomorphic}.

Arguments def_isomorphic {σ A B}.
Arguments is_homomorphism_isomorphic {σ A B}.
Arguments is_isomorphism_isomorphic {σ A B}.

Global Existing Instance is_homomorphism_isomorphic.
Global Existing Instance is_isomorphism_isomorphic.

Module isomorphic_notations.
  Global Notation "A ≅ B" := (Isomorphic A B)
                             (at level 75, no associativity)
                             : Algebra_scope.
End isomorphic_notations.

Import isomorphic_notations.

Definition SigIsomorphic {σ : Signature} (A B : Algebra σ) :=
  { def_iso : ∀ s, A s → B s
  | { _ : IsHomomorphism def_iso | IsIsomorphism def_iso }}.

Lemma issig_isomorphic {σ : Signature} (A B : Algebra σ)
  : SigIsomorphic A B <~> A ≅ B.
Proof.
  issig.
Defined.

(** Isomorphic algebras can be identified [A ≅ B → A = B]. *)

Corollary id_isomorphic `{Univalence} {σ} {A B : Algebra σ} (e : A ≅ B)
  : A = B.
Proof.
  exact (path_isomorphism (def_isomorphic e)).
Defined.

(** Identified algebras are isomorophic [A = B → A ≅ B] *)

Lemma isomorphic_id {σ} {A B : Algebra σ} (p : A = B) : A ≅ B.
Proof.
  destruct p. exact (BuildIsomorphic (hom_id A)).
Defined.

(** To find a path between two witnesses [F G : A ≅ B], it suffices
    to find a path between the defining families of functions and
    the [is_homomorphism_hom] witnesses. *)

Lemma path_isomorphic `{Funext} {σ : Signature} {A B : Algebra σ}
  (F G : A ≅ B) (a : def_isomorphic F = def_isomorphic G)
  (b : a#(is_homomorphism_isomorphic F) = is_homomorphism_isomorphic G)
  : F = G.
Proof.
  apply (ap (issig_isomorphic A B)^-1)^-1.
  serapply path_sigma.
  - exact a.
  - apply path_sigma_hprop.
    refine (ap _ (transport_sigma _ _) @ _).
    apply b.
Defined.

(** Suppose [IsHSetAlgebra B]. To find a path between two isomorphic
    witnesses [F G : A ≅ B], it suffices to find a path between the
    defining families of functions. *)

Lemma path_hset_isomorphic `{Funext} {σ : Signature} {A B : Algebra σ}
  `{IsHSetAlgebra B} (F G : A ≅ B)
  (a : def_isomorphic F = def_isomorphic G)
  : F = G.
Proof.
  apply (path_isomorphic F G a). apply path_ishprop.
Defined.

Section path_def_isomorphic_id_transport.
  Context {σ : Signature} {A B : Algebra σ}.

  Lemma path_def_isomorphic_id_transport_dom (p : A = B)
    : def_isomorphic (isomorphic_id p)
      = transport (λ C, ∀ s, C s → B s) (ap carriers p)^ (hom_id B).
  Proof.
    by path_induction.
  Defined.

  Lemma path_def_isomorphic_id_transport_cod (p : A = B)
    : def_isomorphic (isomorphic_id p)
      = transport (λ C, ∀ s, A s → C s) (ap carriers p) (hom_id A).
  Proof.
    by path_induction.
  Defined.
End path_def_isomorphic_id_transport.

(** If [IsHSetAlgebra A], then [path_isomorphism] maps the identity
    homomorphism of [A] to the identity path. *)

(* I suspect that the following lemma holds even when [A] is not a set
   algebra. To show this, [path_isomorphism] and [path_operations_equiv]
   should be made transparent, which they are not at the moment. *)

Lemma path_path_isomorphism_hom_id_hset `{Univalence} {σ : Signature}
  (A : Algebra σ) `{IsHSetAlgebra A}
  : path_isomorphism (hom_id A) = idpath.
Proof.
  apply path_path_hset_algebra.
  rewrite path_ap_carriers_path_algebra.
  apply (paths_ind (λ s, idpath) (λ f _, path_forall A A f = idpath)).
  - apply path_forall_1.
  - intros.
    funext s.
    symmetry.
    rewrite (path_ishprop _ (isequiv_idmap (A s))).
    apply path_universe_1.
Qed.

(** The following section shows that [isomorphic_id] is an equivalence
    with inverse [id_isomorphic]. *)

Section isequiv_isomorphic_id.
  Context `{Univalence} {σ} (A B : Algebra σ) `{IsHSetAlgebra B}.

  Lemma sect_id_isomorphic : Sect id_isomorphic (@isomorphic_id σ A B).
  Proof.
    intro F.
    apply path_hset_isomorphic.
    rewrite path_def_isomorphic_id_transport_cod.
    funext s x.
    rewrite !transport_forall_constant.
    rewrite path_ap_carriers_path_algebra.
    transport_path_forall_hammer.
    apply transport_path_universe.
  Qed.

  Lemma sect_isomorphic_id : Sect (@isomorphic_id σ A B) id_isomorphic.
  Proof.
    intro p.
    destruct p.
    apply path_path_isomorphism_hom_id_hset.
    exact _.
  Qed.

  Global Instance isequiv_isomorphic_id : IsEquiv (@isomorphic_id σ A B)
    := isequiv_adjointify
          isomorphic_id
          id_isomorphic
          sect_id_isomorphic
          sect_isomorphic_id.

End isequiv_isomorphic_id.
