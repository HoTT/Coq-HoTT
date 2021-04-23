(** This file develops algebra [Isomorphism] and shows it is equivalent to equality. *)

Require Export HoTT.Algebra.Universal.Homomorphism.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.Tactics.

Local Unset Elimination Schemes.

Local Open Scope Algebra_scope.

(** A homomorphism is an isomorphism if it is pointwise an equivalence. *)

Class IsIsomorphism {σ : Signature} {A B : Algebra σ}
  (f : forall s, A s -> B s) `{!IsHomomorphism f}
  := isequiv_isomorphism : forall (s : Sort σ), IsEquiv (f s).

Global Existing Instance isequiv_isomorphism.

Definition equiv_isomorphism {σ : Signature} {A B : Algebra σ}
  (f : forall s, A s -> B s) `{IsIsomorphism σ A B f}
  : forall (s : Sort σ), A s <~> B s.
Proof.
  intro s. rapply (Build_Equiv _ _ (f s)).
Defined.

Global Instance hprop_is_isomorphism `{Funext} {σ : Signature}
  {A B : Algebra σ} (f : forall s, A s -> B s) `{!IsHomomorphism f}
  : IsHProp (IsIsomorphism f).
Proof.
  apply istrunc_forall.
Qed.

(** If there is an isomorphism [f : forall s, A s -> B s] then [A = B]. *)

Section is_isomorphism_to_path.
  Context `{Univalence} {σ : Signature} {A B : Algebra σ}.

  Local Notation path_equiv_family f
    := (path_forall _ _ (fun i => path_universe (f i))).

  Lemma path_operations_equiv {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    (f : forall (s : Sort σ), A s <~> B s) (P : OpPreserving f α β)
    : transport (fun C => Operation C w) (path_equiv_family f) α = β.
  Proof.
    funext a.
    unfold Operation.
    transport_path_forall_hammer.
    rewrite transport_arrow_toconst.
    rewrite transport_forall_constant.
    rewrite transport_idmap_path_universe.
    rewrite P.
    f_ap.
    funext i.
    rewrite transport_forall_constant.
    rewrite <- path_forall_V.
    transport_path_forall_hammer.
    rewrite (transport_path_universe_V (f _)).
    apply eisretr.
  Qed.

  Lemma path_operations_isomorphism (f : forall s, A s -> B s)
    `{IsIsomorphism σ A B f}
    : transport (fun C => forall u, Operation C (σ u))
        (path_equiv_family (equiv_isomorphism f)) (operations A)
      = operations B.
  Proof.
    funext u.
    refine (transport_forall_constant _ _ u @ _).
    now apply path_operations_equiv.
  Qed.

  Theorem is_isomorphism_to_path
    (f : forall s, A s -> B s) `{IsIsomorphism σ A B f}
    : A = B.
  Proof.
    apply (path_algebra _ _ (path_equiv_family (equiv_isomorphism f))).
    apply path_operations_isomorphism.
  Defined.
End is_isomorphism_to_path.

(** Two algebras [A B : Algebra σ] are isomorphic if there is an isomorphism [forall s, A s -> B s]. *)

Record Isomorphism {σ : Signature} (A B : Algebra σ) := Build_Isomorphism
  { def_isomorphism : forall s, A s -> B s
  ; is_homomorphism_isomorphism : IsHomomorphism def_isomorphism
  ; is_isomorphism_isomorphism : IsIsomorphism def_isomorphism }.

Arguments Build_Isomorphism {σ A B} def_isomorphism
            {is_homomorphism_isomorphism} {is_isomorphism_isomorphism}.

Arguments def_isomorphism {σ A B}.
Arguments is_homomorphism_isomorphism {σ A B}.
Arguments is_isomorphism_isomorphism {σ A B}.

Coercion def_isomorphism : Isomorphism >-> Funclass.

Global Existing Instance is_homomorphism_isomorphism.
Global Existing Instance is_isomorphism_isomorphism.

Bind Scope Algebra_scope with Isomorphism.

Infix "≅" := Isomorphism : Algebra_scope.

(** The identity homomorphism is an isomorphism. *)

Section iso_id.
  Context {σ} (A : Algebra σ).

  Global Instance is_isomorphism_id
    : IsIsomorphism (fun s (x : A s) => x).
  Proof.
    intro s. exact _.
  Defined.

  Definition iso_id : A ≅ A
    := Build_Isomorphism (fun s (a : A s) => a).
End iso_id.

Lemma path_is_isomorphism_to_path_id `{Univalence} {σ} (A : Algebra σ)
  : is_isomorphism_to_path (hom_id A) = idpath.
Proof.
  apply path_path_algebra.
  refine (path_ap_carriers_path_algebra _ _ _ _ @ _ @ path_forall_1 A).
  refine (ap _ _).
  funext s.
  apply path_universe_1.
Qed.

(** The composition of isomorphisms is an isomorphism. *)

Section iso_compose.
  Context
    {σ} (A B C : Algebra σ)
    (g : forall s, B s -> C s) `{IsIsomorphism σ B C g}
    (f : forall s, A s -> B s) `{IsIsomorphism σ A B f}.

  Global Instance is_isomorphism_compose
    : IsIsomorphism (fun s => g s o f s).
  Proof.
    intro s. apply isequiv_compose.
  Qed.

  Definition iso_compose : A ≅ C
    := Build_Isomorphism (fun s => g s o f s).
End iso_compose.

(** The inverse of an isomorphism. *)

Section iso_inv.
  Context
    `{Funext} {σ} {A B : Algebra σ}
    (f : forall s, A s -> B s) `{IsIsomorphism σ A B f}.

  Global Instance is_homomorphism_inv : IsHomomorphism (fun s => (f s)^-1).
  Proof.
   intros u a.
   apply (ap (f (sort_cod (σ u))))^-1.
   rewrite (oppreserving_hom f).
   refine (eisretr _ _ @ _).
   f_ap.
   funext i.
   symmetry; apply eisretr.
  Qed.

  Global Instance is_isomorphism_inv : IsIsomorphism (fun s => (f s)^-1).
  Proof.
    intro s. exact _.
  Defined.

  Definition hom_inv : Homomorphism B A
    := Build_Homomorphism (fun s => (f s)^-1).

  Definition iso_inv : B ≅ A
    := Build_Isomorphism (fun s => (f s)^-1).
End iso_inv.

Definition SigIsomorphism {σ : Signature} (A B : Algebra σ) :=
  { def_iso : forall s, A s -> B s
  | { _ : IsHomomorphism def_iso | IsIsomorphism def_iso }}.

Lemma issig_isomorphism {σ : Signature} (A B : Algebra σ)
  : SigIsomorphism A B <~> (A ≅ B).
Proof.
  issig.
Defined.

(** Isomorphic algebras are equal [A ≅ B -> A = B]. *)

Corollary isomorphism_to_path `{Univalence}
  {σ : Signature} {A B : Algebra σ} (e : A ≅ B)
  : A = B.
Proof.
  exact (is_isomorphism_to_path (def_isomorphism e)).
Defined.

(** Equal algebras are isomorphic [A = B -> A ≅ B] *)

Lemma path_to_isomorphism {σ} {A B : Algebra σ} (p : A = B) : A ≅ B.
Proof.
  destruct p. exact (Build_Isomorphism (hom_id A)).
Defined.

(** To find a path between two isomorphisms [F G : A ≅ B], it suffices to find a path between the underlying families of functions. *)

Lemma path_isomorphism `{Funext} {σ : Signature} {A B : Algebra σ}
  (F G : A ≅ B) (a : def_isomorphism F = def_isomorphism G)
  : F = G.
Proof.
  apply (ap (issig_isomorphism A B)^-1)^-1.
  srapply path_sigma.
  - exact a.
  - apply path_sigma_hprop.
    refine (ap _ (transport_sigma _ _) @ _).
    apply path_ishprop.
Defined.

Section path_def_path_to_isomorphism_transport.
  Context {σ : Signature} {A B : Algebra σ}.

  Lemma path_path_to_isomorphism_transportV (p : A = B)
    : def_isomorphism (path_to_isomorphism p)
      = transport (fun C => forall s, C s -> B s) (ap carriers p)^ (hom_id B).
  Proof.
    by path_induction.
  Defined.

  Lemma path_path_to_isomorphism_transport (p : A = B)
    : def_isomorphism (path_to_isomorphism p)
      = transport (fun C => forall s, A s -> C s) (ap carriers p) (hom_id A).
  Proof.
    by path_induction.
  Defined.
End path_def_path_to_isomorphism_transport.

(** The following section shows that [path_to_isomorphism] is an equivalence with inverse [isomorphism_to_path]. *)

Section equiv_path_to_isomorphism.
  Context `{Univalence} {σ} (A B : Algebra σ).

  Lemma path_isomorphism_to_path_to_isomorphism
    : (@path_to_isomorphism σ A B) o isomorphism_to_path == idmap.
  Proof.
    intro F.
    apply path_isomorphism.
    rewrite path_path_to_isomorphism_transport.
    funext s x.
    do 2 rewrite transport_forall_constant.
    rewrite path_ap_carriers_path_algebra.
    transport_path_forall_hammer.
    apply transport_path_universe.
  Qed.

  Lemma path_path_to_isomorphism_to_path
    : isomorphism_to_path o (@path_to_isomorphism σ A B) == idmap.
  Proof.
    intro p.
    destruct p.
    apply path_is_isomorphism_to_path_id.
  Qed.

  Global Instance isequiv_path_to_isomorphism
    : IsEquiv (@path_to_isomorphism σ A B)
    := isequiv_adjointify
          path_to_isomorphism
          isomorphism_to_path
          path_isomorphism_to_path_to_isomorphism
          path_path_to_isomorphism_to_path.

  Definition equiv_path_to_isomorphism : (A = B) <~> (A ≅ B)
    := Build_Equiv _ _ path_to_isomorphism _.

End equiv_path_to_isomorphism.

