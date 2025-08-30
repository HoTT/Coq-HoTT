(** This file implements algebra homomorphism. We show that algebras form a wild category with homomorphisms. The [WildCat] module provides some nice notations that we use: [A $-> B] for homomorphism, [Id] for the identity homomorphism and [g $o f] for composition. *)

Local Unset Elimination Schemes.

Require Export
  HoTT.Algebra.Universal.Algebra
  HoTT.WildCat.Core.

Require Import
  HoTT.Types.

Local Open Scope Algebra_scope.

Section is_homomorphism.
  Context {σ} {A B : Algebra σ} (f : forall (s : Sort σ), A s -> B s).

  Definition OpPreserving {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) : Type
    := forall a : DomOperation A w,
        f (sort_cod w) (α a) = β (fun i => f (sorts_dom w i) (a i)).

  #[export] Instance hprop_oppreserving `{Funext} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    : IsHProp (OpPreserving α β).
  Proof.
    exact istrunc_forall.
  Qed.

  Class IsHomomorphism : Type
    := oppreserving_hom : forall (u : Symbol σ), OpPreserving u.#A u.#B.

  #[export] Instance hprop_is_homomorphism `{Funext}
    : IsHProp IsHomomorphism.
  Proof.
    exact istrunc_forall.
  Qed.
End is_homomorphism.

Record Homomorphism {σ} {A B : Algebra σ} : Type := Build_Homomorphism
  { def_homomorphism : forall (s : Sort σ), A s -> B s
  ; is_homomorphism :: IsHomomorphism def_homomorphism }.

Arguments Homomorphism {σ}.

Arguments Build_Homomorphism {σ A B} def_homomorphism {is_homomorphism}.

Global Coercion def_homomorphism : Homomorphism >-> Funclass.

Instance isgraph_algebra (σ : Signature) : IsGraph (Algebra σ)
  := Build_IsGraph (Algebra σ) Homomorphism.

Lemma apD10_homomorphism {σ} {A B : Algebra σ} {f g : A $-> B}
  : f = g -> forall s, f s == g s.
Proof.
  intro p. by destruct p.
Defined.

Definition SigHomomorphism {σ} (A B : Algebra σ) : Type :=
  { def_hom : forall s, A s -> B s | IsHomomorphism def_hom }.

Lemma issig_homomorphism {σ} (A B : Algebra σ)
  : SigHomomorphism A B <~> (A $-> B).
Proof.
  issig.
Defined.

Instance hset_homomorphism `{Funext} {σ} (A B : Algebra σ)
  : IsHSet (A $-> B).
Proof.
  exact (istrunc_equiv_istrunc _ (issig_homomorphism A B)).
Qed.

Lemma path_homomorphism `{Funext} {σ} {A B : Algebra σ}
  (f g : A $-> B) (p : def_homomorphism f = def_homomorphism g)
  : f = g.
Proof.
  apply (ap (issig_homomorphism A B)^-1)^-1.
  unfold issig_homomorphism; cbn.
  apply path_sigma_hprop.
  exact p.
Defined.

(** The identity homomorphism. *)

Section homomorphism_id.
  Context {σ} (A : Algebra σ).

  #[export] Instance is_homomorphism_id
    : IsHomomorphism (fun s (x : A s) => x).
  Proof.
    intros u a. reflexivity.
  Defined.

  Definition homomorphism_id : A $-> A
    := Build_Homomorphism (fun s (x : A s) => x).

End homomorphism_id.

Arguments homomorphism_id {σ} A%_Algebra_scope , {σ} {A}.

(** Composition of homomorphisms. *)

Section homomorphism_compose.
  Context {σ} {A B C : Algebra σ}.

  #[export] Instance is_homomorphism_compose
    (g : forall s, B s -> C s) `{!IsHomomorphism g}
    (f : forall s, A s -> B s) `{!IsHomomorphism f}
    : IsHomomorphism (fun s => g s o f s).
  Proof.
    intros u a.
    by rewrite <- (oppreserving_hom g), (oppreserving_hom f).
  Qed.

  Definition homomorphism_compose (g : B $-> C) (f : A $-> B) : A $-> C
    := Build_Homomorphism (fun s => g s o f s).

End homomorphism_compose.

Instance is01cat_algebra (σ : Signature) : Is01Cat (Algebra σ)
  := Build_Is01Cat _ _
      (fun _ => homomorphism_id) (fun _ _ _ => homomorphism_compose).

Lemma assoc_homomorphism_compose `{Funext} {σ}
  {A B C D : Algebra σ} (h : C $-> D) (g : B $-> C) (f : A $-> B)
  : (h $o g) $o f = h $o (g $o f).
Proof.
  by apply path_homomorphism.
Defined.

Lemma left_id_homomorphism_compose `{Funext} {σ}
  {A B : Algebra σ} (f : A $-> B)
  : Id B $o f = f.
Proof.
  by apply path_homomorphism.
Defined.

Lemma right_id_homomorphism_compose `{Funext} {σ}
  {A B : Algebra σ} (f : A $-> B)
  : f $o Id A = f.
Proof.
  by apply path_homomorphism.
Defined.

Instance is2graph_algebra {σ} : Is2Graph (Algebra σ)
  := fun A B
    => Build_IsGraph _ (fun (f g : A $-> B) => forall s, f s == g s).

Instance is01cat_homomorphism {σ} (A B : Algebra σ)
  : Is01Cat (A $-> B).
Proof.
  apply Build_Is01Cat.
  - exact (fun f s x => idpath).
  - exact (fun f g h P Q s x => Q s x @ P s x).
Defined.

Instance is0gpd_homomorphism {σ} {A B : Algebra σ}
  : Is0Gpd (A $-> B).
Proof.
  apply Build_Is0Gpd. intros f g P s x. exact (P s x)^.
Defined.

Instance is0functor_postcomp_homomorphism {σ}
  (A : Algebra σ) {B C : Algebra σ} (h : B $-> C)
  : Is0Functor (@cat_postcomp (Algebra σ) _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p s x.
  exact (ap (h s) (p s x)).
Defined.

Instance is0functor_precomp_homomorphism {σ}
  {A B : Algebra σ} (h : A $-> B) (C : Algebra σ)
  : Is0Functor (@cat_precomp (Algebra σ) _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p s x.
  exact (p s (h s x)).
Defined.

Instance is1cat_algebra (σ : Signature) : Is1Cat (Algebra σ).
Proof.
  by rapply Build_Is1Cat.
Defined.

Instance is1cat_strong_algebra `{Funext} (σ : Signature)
  : Is1Cat_Strong (Algebra σ).
Proof.
  rapply Build_Is1Cat_Strong.
  - intros. apply assoc_homomorphism_compose.
  - intros. symmetry; apply assoc_homomorphism_compose.
  - intros. apply left_id_homomorphism_compose.
  - intros. apply right_id_homomorphism_compose.
Defined.

