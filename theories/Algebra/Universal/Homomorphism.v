(** Thie file implements algebra homomorphism and isomorphim.
    The main theorem in this file is the [isomorphism_to_path] theorem,
    which states that there is a path between isomorphic algebras. *)

Local Unset Elimination Schemes.

Require Export HoTT.Algebra.Universal.Algebra.

Require Import
  HoTT.Types
  HoTT.Tactics.

Import notations_algebra.

Section is_homomorphism.
  Context {σ} {A B : Algebra σ} (f : forall (s : Sort σ), A s -> B s).

  Definition OpPreserving {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) : Type
    := forall a : DomOperation A w,
        f (sort_cod w) (α a) = β (fun i => f (sorts_dom w i) (a i)).

  Global Instance hprop_oppreserving `{Funext} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    : IsHProp (OpPreserving α β).
  Proof.
    apply trunc_forall.
  Qed.

  Class IsHomomorphism : Type
    := oppreserving_hom : forall (u : Symbol σ), OpPreserving u^^A u^^B.

  Global Instance hprop_is_homomorphism `{Funext}
    : IsHProp IsHomomorphism.
  Proof.
    apply trunc_forall.
  Qed.
End is_homomorphism.

Record Homomorphism {σ} {A B : Algebra σ} : Type := Build_Homomorphism
  { def_hom : forall (s : Sort σ), A s -> B s
  ; is_homomorphism_hom : IsHomomorphism def_hom }.

Arguments Homomorphism {σ}.

Arguments Build_Homomorphism {σ A B} def_hom {is_homomorphism_hom}.

Global Coercion def_hom : Homomorphism >-> Funclass.

Global Existing Instance is_homomorphism_hom.

Lemma apD10_homomorphism {σ} {A B : Algebra σ} {f g : Homomorphism A B}
  : f = g -> forall s, f s == g s.
Proof.
  intro p. by destruct p.
Defined.

Definition SigHomomorphism {σ} (A B : Algebra σ) : Type :=
  { def_hom : forall s, A s -> B s | IsHomomorphism def_hom }.

Lemma issig_homomorphism {σ} (A B : Algebra σ)
  : SigHomomorphism A B <~> Homomorphism A B.
Proof.
  issig.
Defined.

Global Instance hset_homomorphism `{Funext} {σ} (A B : Algebra σ)
  : IsHSet (Homomorphism A B).
Proof.
  apply (trunc_equiv _ (issig_homomorphism A B)).
Qed.

Lemma path_homomorphism `{Funext} {σ} {A B : Algebra σ}
  (f g : Homomorphism A B) (p : def_hom f = def_hom g)
  : f = g.
Proof.
  apply (ap (issig_homomorphism A B)^-1)^-1.
  unfold issig_homomorphism; cbn.
  apply path_sigma_hprop.
  exact p.
Defined.

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
  apply trunc_forall.
Qed.

(** The identity homomorphism. *)

Section hom_id.
  Context {σ} (A : Algebra σ).

  Global Instance is_homomorphism_id
    : IsHomomorphism (fun s (x : A s) => x).
  Proof.
    intros u a. reflexivity.
  Defined.

  Global Instance is_isomorphism_id
    : IsIsomorphism (fun s (x : A s) => x).
  Proof.
    intro s. exact _.
  Defined.

  Definition hom_id : Homomorphism A A
    := Build_Homomorphism (fun s (x : A s) => x).

End hom_id.

Arguments hom_id {σ} A%Algebra_scope , {σ} {A}.

(** Composition of homomorphisms. *)

Section hom_compose.
  Context {σ} {A B C : Algebra σ}.

  Global Instance is_homomorphism_compose
    (g : forall s, B s -> C s) `{!IsHomomorphism g}
    (f : forall s, A s -> B s) `{!IsHomomorphism f}
    : IsHomomorphism (fun s => g s o f s).
  Proof.
    intros u a.
    by rewrite <- (oppreserving_hom g), (oppreserving_hom f).
  Qed.

  Global Instance is_isomorphism_compose
    (g : forall s, B s -> C s) `{IsIsomorphism σ B C g}
    (f : forall s, A s -> B s) `{IsIsomorphism σ A B f}
    : IsIsomorphism (fun s => g s o f s).
  Proof.
    intro s. apply isequiv_compose.
  Qed.

  Definition hom_compose
    (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
    := Build_Homomorphism (fun s => g s o f s).

End hom_compose.

Lemma assoc_hom_compose `{Funext} {σ} {A B C D : Algebra σ}
    (h : Homomorphism C D) (g : Homomorphism B C) (f : Homomorphism A B)
    : hom_compose h (hom_compose g f) = hom_compose (hom_compose h g) f.
Proof.
  by apply path_homomorphism.
Defined.

Lemma left_id_hom_compose `{Funext} {σ} {A B : Algebra σ}
    (f : Homomorphism A B)
    : hom_compose hom_id f = f.
Proof.
  by apply path_homomorphism.
Defined.

Lemma right_id_hom_compose `{Funext} {σ} {A B : Algebra σ}
    (f : Homomorphism A B)
    : hom_compose f hom_id = f.
Proof.
  by apply path_homomorphism.
Defined.

(** The inverse of an isomorphism. *)

Section hom_inv.
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

End hom_inv.

(** If there is an isomorphism [f : forall s, A s -> B s] then [A = B]. *)

Section isomorphism_to_path.
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

  Theorem isomorphism_to_path (f : forall s, A s -> B s) `{IsIsomorphism σ A B f}
    : A = B.
  Proof.
    apply (path_algebra _ _ (path_equiv_family (equiv_isomorphism f))).
    apply path_operations_isomorphism.
  Defined.
End isomorphism_to_path.
