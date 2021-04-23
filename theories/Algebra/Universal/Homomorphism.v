(** Thie file implements algebra homomorphism. *)

Local Unset Elimination Schemes.

Require Export HoTT.Algebra.Universal.Algebra.

Require Import
  HoTT.Types
  HoTT.Tactics.

Local Open Scope Algebra_scope.

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
    apply istrunc_forall.
  Qed.

  Class IsHomomorphism : Type
    := oppreserving_hom : forall (u : Symbol σ), OpPreserving u.#A u.#B.

  Global Instance hprop_is_homomorphism `{Funext}
    : IsHProp IsHomomorphism.
  Proof.
    apply istrunc_forall.
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
  apply (istrunc_equiv_istrunc _ (issig_homomorphism A B)).
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

(** The identity homomorphism. *)

Section hom_id.
  Context {σ} (A : Algebra σ).

  Global Instance is_homomorphism_id
    : IsHomomorphism (fun s (x : A s) => x).
  Proof.
    intros u a. reflexivity.
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
