(** This file implements [IsHomomorphism] and [IsIsomorphism].
    It developes basic algebra homomorphisms and isomorphims. The main
    theorem in this file is the [path_isomorphism] theorem, which
    states that there is a path between isomorphic algebras. *)

Require Export HoTT.Classes.interfaces.ua_setalgebra.

Require Import
  HoTT.Types
  HoTT.Tactics.

Import algebra_notations ne_list.notations.

Section is_homomorphism.
  Context {σ} {A B : Algebra σ} (f : ∀ (s : Sort σ), A s → B s).

(** The family of functions [f] above is [OpPreserving α β] with
    respect to operations [α : A s1 → A s2 → ... → A sn → A t] and
    [β : B s1 → B s2 → ... → B sn → B t] if

<<
      f t (α x1 x2 ... xn) = β (f s1 x1) (f s2 x2) ... (f sn xn)
>>
*)

  Fixpoint OpPreserving {w : SymbolType σ}
    : Operation A w → Operation B w → Type
    := match w with
       | [:s:] => λ α β, f s α = β
       | s ::: y => λ α β, ∀ (x : A s), OpPreserving (α x) (β (f s x))
       end.

  Global Instance trunc_oppreserving `{Funext} {n : trunc_index}
    `{!IsTruncAlgebra n.+1 B} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    : IsTrunc n (OpPreserving α β).
  Proof.
    induction w; exact _.
  Qed.

(** The family of functions [f : ∀ (s : Sort σ), A s → B s] above is
    a homomorphism if for each function symbol [u : Symbol σ], it is
    [OpPreserving u.#A u.#B] with respect to the algebra
    operations [u.#A] and [u.#B] corresponding to [u]. *)

  Class IsHomomorphism : Type
    := oppreserving_hom : ∀ (u : Symbol σ), OpPreserving u.#A u.#B.

  Global Instance trunc_is_homomorphism `{Funext} {n : trunc_index}
    `{!IsTruncAlgebra n.+1 B}
    : IsTrunc n IsHomomorphism.
  Proof.
    apply istrunc_forall.
  Qed.
End is_homomorphism.

Record Homomorphism {σ} {A B : Algebra σ} : Type := BuildHomomorphism
  { def_hom : ∀ (s : Sort σ), A s → B s
  ; is_homomorphism_hom : IsHomomorphism def_hom }.

Arguments Homomorphism {σ}.

Arguments BuildHomomorphism {σ A B} def_hom {is_homomorphism_hom}.

(** We the implicit coercion from [Homomorphism A B] to the family
    of functions [∀ s, A s → B s]. *)

Global Coercion def_hom : Homomorphism >-> Funclass.

Global Existing Instance is_homomorphism_hom.

Lemma apD10_homomorphism {σ} {A B : Algebra σ} {f g : Homomorphism A B}
  : f = g → ∀ s, f s == g s.
Proof.
  intro p. by destruct p.
Defined.

Definition SigHomomorphism {σ} (A B : Algebra σ) : Type :=
  { def_hom : ∀ s, A s → B s | IsHomomorphism def_hom }.

Lemma issig_homomorphism {σ} (A B : Algebra σ)
  : SigHomomorphism A B <~> Homomorphism A B.
Proof.
  issig.
Defined.

Global Instance trunc_homomorphism `{Funext} {σ} {A B : Algebra σ}
  {n : trunc_index} `{!IsTruncAlgebra n B}
  : IsTrunc n (Homomorphism A B).
Proof.
  apply (istrunc_equiv_istrunc _ (issig_homomorphism A B)).
Qed.

(** To find a path between two homomorphisms [f g : Homomorphism A B]
    it suffices to find a path between the defining families of
    functions and the [is_homomorphism_hom] witnesses. *)

Lemma path_homomorphism {σ} {A B : Algebra σ} (f g : Homomorphism A B)
  (p : def_hom f = def_hom g)
  (q : p#(is_homomorphism_hom f) = is_homomorphism_hom g)
  : f = g.
Proof.
  destruct f, g. simpl in *. by path_induction.
Defined.

(** To find a path between two homomorphisms [f g : Homomorphism A B]
    it suffices to find a path between the defining families of
    functions if [IsHSetAlgebra B]. *)

Lemma path_hset_homomorphism `{Funext} {σ} {A B : Algebra σ}
  `{!IsHSetAlgebra B} (f g : Homomorphism A B)
  (p : def_hom f = def_hom g)
  : f = g.
Proof.
  apply (path_homomorphism f g p). apply path_ishprop.
Defined.

(** A family of functions [f : ∀ s, A s → B s] is an isomorphism if it is
    a homomorphism, and for each [s : Sort σ], [f s] is an equivalence. *)

(* We make [IsHomomorphism] an argument here, rather than a field, so
   having both [f : Homomorphism A B] and [X : IsIsomorphism f] in
   context does not result in having two proofs of [IsHomomorphism f]
   in context. *)

Class IsIsomorphism {σ : Signature} {A B : Algebra σ}
  (f : ∀ s, A s → B s) `{!IsHomomorphism f}
  := isequiv_isomorphism : ∀ (s : Sort σ), IsEquiv (f s).

Global Existing Instance isequiv_isomorphism.

Definition equiv_isomorphism {σ : Signature} {A B : Algebra σ}
  (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}
  : ∀ (s : Sort σ), A s <~> B s.
Proof.
  intro s. rapply (Build_Equiv _ _ (f s)).
Defined.

Global Instance hprop_is_isomorphism `{Funext} {σ : Signature}
  {A B : Algebra σ} (f : ∀ s, A s → B s) `{!IsHomomorphism f}
  : IsHProp (IsIsomorphism f).
Proof.
  apply istrunc_forall.
Qed.

(** Let [f : ∀ s, A s → B s] be a homomorphism. The following
    section proves that [f] is "OpPreserving" with respect to
    uncurried algebra operations in the sense that

<<
      f t (α (x1,x2,...,xn,tt)) = β (f s1 x1,f s2 x1,...,f sn xn,tt)
>>

    for all [(x1,x2,...,xn,tt) : FamilyProd A [s1;s2;...;sn]], where
    [α] and [β] are uncurried algebra operations in [A] and [B]
    respectively.
*)

Section homomorphism_ap_operation.
  Context {σ : Signature} {A B : Algebra σ}.

  Lemma path_oppreserving_ap_operation (f : ∀ s, A s → B s)
    {w : SymbolType σ} (a : FamilyProd A (dom_symboltype w))
    (α : Operation A w) (β : Operation B w) (P : OpPreserving f α β)
    : f (cod_symboltype w) (ap_operation α a)
      = ap_operation β (map_family_prod f a).
  Proof.
    induction w.
    - assumption.
    - destruct a as [x a]. apply IHw. apply P.
  Defined.

(** A homomorphism [f : ∀ s, A s → B s] satisfies

<<
      f t (α (a1, a2, ..., an, tt))
      = β (f s1 a1, f s2 a2, ..., f sn an, tt)
>>

    where [(a1, a2, ..., an, tt) : FamilyProd A [s1; s2; ...; sn]] and
    [α], [β] uncurried versions of [u.#A], [u.#B] respectively. *)

  Lemma path_homomorphism_ap_operation (f : ∀ s, A s → B s)
    `{!IsHomomorphism f}
    : ∀ (u : Symbol σ) (a : FamilyProd A (dom_symboltype (σ u))),
      f (cod_symboltype (σ u)) (ap_operation u.#A a)
      = ap_operation u.#B (map_family_prod f a).
  Proof.
    intros u a. by apply path_oppreserving_ap_operation.
  Defined.
End homomorphism_ap_operation.

(** The next section shows that the family of identity functions,
    [λ s x, x] is an isomorphism. *)

Section hom_id.
  Context {σ} (A : Algebra σ).

  Global Instance is_homomorphism_id
    : IsHomomorphism (λ s (x : A s), x).
  Proof.
    intro u. generalize u.#A. intro w. induction (σ u).
    - reflexivity.
    - by intro x.
  Defined.

  Global Instance is_isomorphism_id
    : IsIsomorphism (λ s (x : A s), x).
  Proof.
    intro s. exact _.
  Qed.

  Definition hom_id : Homomorphism A A
    := BuildHomomorphism (λ s x, x).

End hom_id.

(** Suppose [f : ∀ s, A s → B s] is an isomorphism. The following
    section shows that the family of inverse functions, [λ s, (f s)^-1]
    is an isomorphism. *)

Section hom_inv.
  Context
    {σ} {A B : Algebra σ}
    (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}.

  Global Instance is_homomorphism_inv : IsHomomorphism (λ s, (f s)^-1).
  Proof.
   intro u.
   generalize u.#A u.#B (oppreserving_hom f u).
   intros a b P.
   induction (σ u).
   - destruct P. apply (eissect (f t)).
   - intro. apply IHs.
     exact (transport (λ y, OpPreserving f _ (b y))
              (eisretr (f t) x) (P (_^-1 x))).
  Defined.

  Global Instance is_isomorphism_inv : IsIsomorphism (λ s, (f s)^-1).
  Proof.
    intro s. exact _.
  Qed.

  Definition hom_inv : Homomorphism B A
    := BuildHomomorphism (λ s, (f s)^-1).

End hom_inv.

(** Let [f : ∀ s, A s → B s] and [g : ∀ s, B s → C s]. The
    next section shows that composition given by [λ (s : Sort σ),
    g s o f s] is again a homomorphism. If both [f] and [g] are
    isomorphisms, then the composition is an isomorphism. *)

Section hom_compose.
  Context {σ} {A B C : Algebra σ}.

  Lemma oppreserving_compose (g : ∀ s, B s → C s) `{!IsHomomorphism g}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) (γ : Operation C w)
    (G : OpPreserving g β γ) (F : OpPreserving f α β)
    : OpPreserving (λ s, g s o f s) α γ.
  Proof.
    induction w; simpl in *.
    - by path_induction.
    - intro x. by apply (IHw _ (β (f _ x))).
  Defined.

  Global Instance is_homomorphism_compose
    (g : ∀ s, B s → C s) `{!IsHomomorphism g}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f}
    : IsHomomorphism (λ s, g s o f s).
  Proof.
    intro u.
    by apply (oppreserving_compose g f u.#A u.#B u.#C).
  Defined.

  Global Instance is_isomorphism_compose
    (g : ∀ s, B s → C s) `{IsIsomorphism σ B C g}
    (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}
    : IsIsomorphism (λ s, g s o f s).
  Proof.
    intro s. apply isequiv_compose.
  Qed.

  Definition hom_compose
    (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
    := BuildHomomorphism (λ s, g s o f s).

End hom_compose.

(** The following section shows that there is a path between
    isomorphic algebras. *)

Section path_isomorphism.
  Context `{Univalence} {σ : Signature} {A B : Algebra σ}.

(** Let [F G : I → Type]. If [f : ∀ (i:I), F i <~> G i] is a family of
    equivalences, then by function extensionality composed with
    univalence there is a path [F = G]. *)

  Local Notation path_equiv_family f
    := (path_forall _ _ (λ i, path_universe (f i))).

(** Given a family of equivalences [f : ∀ (s : Sort σ), A s <~> B s]
    which is [OpPreserving f α β] with respect to algebra operations

<<
      α : A s1 → A s2 → ... → A sn → A t
      β : B s1 → B s2 → ... → B sn → B t
>>

    By transporting [α] along the path [path_equiv_family f] we
    find a path from the transported operation [α] to [β]. *)

  Lemma path_operations_equiv {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    (f : ∀ (s : Sort σ), A s <~> B s) (P : OpPreserving f α β)
    : transport (λ C : Carriers σ, Operation C w)
        (path_equiv_family f) α
      = β.
  Proof.
    induction w; simpl in *.
    - transport_path_forall_hammer.
      exact (ap10 (transport_idmap_path_universe (f t)) α @ P).
    - funext y.
      transport_path_forall_hammer.
      rewrite transport_forall_constant.
      rewrite transport_arrow_toconst.
      rewrite (transport_path_universe_V (f t)).
      apply IHw.
      specialize (P ((f t)^-1 y)).
      by rewrite (eisretr (f t) y) in P.
  Qed.

(** Suppose [u : Symbol σ] is a function symbol. Recall that
    [u.#A] is notation for [operations A u : Operation A (σ u)]. This
    is the algebra operation corresponding to function symbol [u]. *)

(** An isomorphism [f : ∀ s, A s → B s] induces a family of
    equivalences [e : ∀ (s : Sort σ), A s <~> B s]. Let [u : Symbol σ]
    be a function symbol. Since [f] is a homomorphism, the induced
    family of equivalences [e] satisfies [OpPreserving e (u.#A) (u.#B)].
    By [path_operations_equiv] above, we can then transport [u.#A] along
    the path [path_equiv_family e] and obtain a path to [u.#B]. *)

  Lemma path_operations_isomorphism (f : ∀ s, A s → B s)
    `{IsIsomorphism σ A B f} (u : Symbol σ)
    : transport (λ C : Carriers σ, Operation C (σ u))
        (path_equiv_family (equiv_isomorphism f)) u.#A
      = u.#B.
  Proof.
    by apply path_operations_equiv.
  Defined.

(** If there is an isomorphism [f : ∀ s, A s → B s] then [A = B]. *)

  Theorem path_isomorphism (f : ∀ s, A s → B s) `{IsIsomorphism σ A B f}
    : A = B.
  Proof.
    apply (path_algebra _ _ (path_equiv_family (equiv_isomorphism f))).
(* Make the last part abstract because it relies on [path_operations_equiv],
   which is opaque. In cases where the involved algebras are set algebras,
   then this part is a mere proposition. *)
    abstract (
      funext u;
      exact (transport_forall_constant _ _ u
             @ path_operations_isomorphism f u)).
  Defined.
End path_isomorphism.
