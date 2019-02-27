(** This file implements [IsHomomorphism] and [IsIsomorphism].
    It developes basic algebra homomorphisms and isomorphims. The main
    theorem in this file is the [path_isomorphism] theorem, which
    states that there is a path between isomorphic algebras. *)

Require Import
  HoTT.Basics.Equivalences
  HoTT.Basics.PathGroupoids
  HoTT.Types.Forall
  HoTT.Types.Arrow
  HoTT.Types.Universe
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.Fibrations
  HoTT.HSet
  HoTT.Tactics
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.ua_algebra.

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
  Defined.

(** The family of functions [f : ∀ (s : Sort σ), A s → B s] above is
    a homomorphism if for each function symbol [u : Symbol σ], it is
    [OpPreserving (u^^A) (u^^B)] with respect to the algebra
    operations [u^^A] and [u^^B] corresponding to [u]. *)

  Class IsHomomorphism : Type
    := oppreserving_hom : ∀ (u : Symbol σ), OpPreserving (u^^A) (u^^B).

  Global Instance trunc_is_homomorphism `{Funext} {n : trunc_index}
    `{!IsTruncAlgebra n.+1 B}
    : IsTrunc n IsHomomorphism.
  Proof.
    apply trunc_forall.
  Defined.
End is_homomorphism.

(** A family of functions [f : ∀ s, A s → B s] is an isomorphism if it is
    a homomorphism, and for each [s : Sort σ], [f s] is an equivalence. *)

Class IsIsomorphism {σ} {A B : Algebra σ} (f : ∀ s, A s → B s) :=
  BuildIsIsomorphism
    { ishom_isomorphism : IsHomomorphism f
    ; isequiv_isomorphism : ∀ (s : Sort σ), IsEquiv (f s) }.

Global Existing Instance ishom_isomorphism.

Global Existing Instance isequiv_isomorphism.

Definition equiv_isomorphism {σ : Signature} {A B : Algebra σ}
  (f : ∀ s, A s → B s) `{!IsIsomorphism f}
  : ∀ (s : Sort σ), A s <~> B s.
Proof.
  intro s. rapply (BuildEquiv _ _ (f s)).
Defined.

Definition SigIsIsomorphism {σ} {A B : Algebra σ} (f : ∀ s, A s → B s)
  := { _ : IsHomomorphism f | ∀ s, IsEquiv (f s) }.

Lemma issig_is_isomorphism {σ} {A B : Algebra σ} (f : ∀ s, A s → B s)
  : SigIsIsomorphism f <~> IsIsomorphism f.
Proof.
  unfold SigIsIsomorphism.
  issig (@BuildIsIsomorphism σ A B f)
          (@ishom_isomorphism σ A B f) (@isequiv_isomorphism σ A B f).
Defined.

Global Instance trunc_sig_is_isomorphism `{Funext} {σ : Signature}
  {A B : Algebra σ} {n} `{!IsTruncAlgebra n.+2 B} (f : ∀ s, A s → B s)
  : IsTrunc n.+1 (SigIsIsomorphism f).
Proof.
  apply @trunc_sigma.
  - exact _.
  - intros. apply (@trunc_leq -1).
    + by destruct n.
    + apply trunc_forall.
Defined.

Global Instance trunc_is_isomorphism `{Funext} {σ : Signature}
  {A B : Algebra σ} {n} `{!IsTruncAlgebra n.+2 B} (f : ∀ s, A s → B s)
  : IsTrunc n.+1 (IsIsomorphism f).
Proof.
  apply (trunc_equiv _ (issig_is_isomorphism f)).
Defined.

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

  Lemma path_homomorphism_ap_operation (f : ∀ s, A s → B s) `{!IsHomomorphism f}
    : ∀ (u : Symbol σ) (a : FamilyProd A (dom_symboltype (σ u))),
      f (cod_symboltype (σ u)) (ap_operation (u^^A) a)
      = ap_operation (u^^B) (map_family_prod f a).
  Proof.
    intros u a. by apply path_oppreserving_ap_operation.
  Defined.
End homomorphism_ap_operation.

(** The next section shows that the family of identity functions,
    [f s x = x] is an isomorphism. *)

Section hom_id.
  Context {σ} (A : Algebra σ).

  Definition hom_id (s : Sort σ) : A s → A s := idmap.

  Global Instance is_isomorphism_id : IsIsomorphism hom_id.
  Proof.
  constructor.
  - intro u. generalize (u^^A). intro w. induction (σ u).
    + reflexivity.
    + now intro x.
  - intro s. exact _.
  Defined.
End hom_id.

(** Suppose [f : ∀ s, A s → B s] is an isomorphism. The next
    section provides an inverse homomorphism [g : ∀ s, B s → A s],
    which is also an isomorphism [IsIsomorphism g]. *)

Section hom_inv.
  Context
    {σ} {A B : Algebra σ} (f : ∀ s, A s → B s) `{!IsIsomorphism f}.

  Definition hom_inv (s : Sort σ) : B s → A s := (f s)^-1.

  Global Instance is_isomorphism_inv : IsIsomorphism hom_inv.
  Proof.
   constructor.
   - intro u.
     generalize (u^^A) (u^^B) (oppreserving_hom f u).
     intros a b P.
     induction (σ u).
     + destruct P. apply (eissect (f t)).
     + intro. apply IHs.
       exact (transport (λ y, OpPreserving f _ (b y))
                (eisretr (f t) x) (P (_^-1 x))).
  - intro s. exact _.
  Defined.
End hom_inv.

(** Let [f : ∀ s, A s → B s] and [g : ∀ s, B s → C s]. The
    following section shows that composition given by [λ (s : Sort σ),
    g s o f s] is again a homomorphism. If both [f] and [g] are
    isomorphisms, then the composition is an isomorphism. *)

Section hom_compose.
  Context {σ} {A B C : Algebra σ}.

  Definition hom_compose (g : ∀ s, B s → C s) `{!IsHomomorphism g}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} (s : Sort σ)
    : A s → C s
    := g s o f s.

  Lemma oppreserving_compose (g : ∀ s, B s → C s) `{!IsHomomorphism g}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w) (γ : Operation C w)
    (G : OpPreserving g β γ) (F : OpPreserving f α β)
    : OpPreserving (hom_compose g f) α γ.
  Proof.
    induction w; simpl in *.
    - by path_induction.
    - intro x. unfold hom_compose. now apply (IHw _ (β (f _ x))).
  Defined.

  Global Instance is_homomorphism_compose
    (g : ∀ s, B s → C s) `{!IsHomomorphism g}
    (f : ∀ s, A s → B s) `{!IsHomomorphism f}
    : IsHomomorphism (hom_compose g f).
  Proof.
    intro u.
    by apply (oppreserving_compose g f (u^^A) (u^^B) (u^^C)).
  Defined.

  Global Instance is_isomorphism_compose
    (g : ∀ s, B s → C s) `{!IsIsomorphism g}
    (f : ∀ s, A s → B s) `{!IsIsomorphism f}
    : IsIsomorphism (hom_compose g f).
  Proof.
    constructor; intros; exact _.
  Qed.
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
    [u^^A] is notation for [operations A u : Operation A (σ u)]. This
    is the algebra operation corresponding to function symbol [u]. *)

(** An isomorphism [f : ∀ s, A s → B s] induces a family of
    equivalences [e : ∀ (s : Sort σ), A s <~> B s]. Let [u : Symbol σ]
    be a function symbol. Since [f] is a homomorphism, the induced
    family of equivalences [e] satisfies [OpPreserving e (u^^A) (u^^B)].
    By [path_operations_equiv] above, we can then transport [u^^A] along
    the path [path_equiv_family e] and obtain a path to [u^^B]. *)

  Lemma path_operations_isomorphism (f : ∀ s, A s → B s)
    `{!IsIsomorphism f} (u : Symbol σ)
    : transport (λ C : Carriers σ, Operation C (σ u))
        (path_equiv_family (equiv_isomorphism f)) (u^^A)
      = u^^B.
  Proof.
    apply path_operations_equiv. apply ishom_isomorphism.
  Defined.

(** If there is an isomorphism [f : ∀ s, A s → B s] then [A = B]. *)

  Theorem path_isomorphism (f : ∀ s, A s → B s) `{!IsIsomorphism f}
    : A = B.
  Proof.
    apply (path_algebra _ _
             (path_equiv_family (equiv_isomorphism f))).
    funext u.
    exact (transport_forall_constant _ _ u
           @ path_operations_isomorphism f u).
  Defined.
End path_isomorphism.
