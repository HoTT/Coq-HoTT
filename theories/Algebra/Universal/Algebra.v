(** This file defines [Algebra], which is a generalization of group,
    ring, module, etc. An [Algebra] moreover generalizes structures
    with infinitary operations, such as infinite complete lattice. *)

Local Unset Elimination Schemes.

Require Export HoTT.Basics.

Require Import
  HoTT.Types.

Declare Scope Algebra_scope.
Delimit Scope Algebra_scope with Algebra.

(** The below definition [SymbolTypeOf] is used to specify algebra
    operations. See [SymbolType] and [Operation] below. *)

Record SymbolTypeOf {Sort : Type} := Build_SymbolTypeOf
  { Arity : Type
  ; sorts_dom : Arity -> Sort
  ; sort_cod : Sort }.

Arguments SymbolTypeOf : clear implicits.
Arguments Build_SymbolTypeOf {Sort}.

(** A [Signature] is used to specify [Algebra]s. A signature describes
    which operations (functions) an algebra for the signature is
    expected to provide. A signature consists of
    - A type of [Sort]s. An algebra for the signature provides
      a type for each [Sort] element.
    - A type of function symbols [Symbol]. For each function symbol
      [u : Symbol], an algebra for the signature provides a
      corresponding operation.
    - The field [symbol_types σ u] indicates which type the operation
      corresponding to [u] is expected to have. *)

Record Signature := Build_Signature
  { Sort : Type
  ; Symbol : Type
  ; symbol_types : Symbol -> SymbolTypeOf Sort
  ; hset_sort : IsHSet Sort
  ; hset_symbol : IsHSet Symbol }.

Notation SymbolType σ := (SymbolTypeOf (Sort σ)).

Global Existing Instance hset_sort.

Global Existing Instance hset_symbol.

Global Coercion symbol_types : Signature >-> Funclass.

(** Each [Algebra] has a collection of carrier types [Carriers σ],
    indexed by the type of sorts [Sort σ]. *)

Notation Carriers σ := (Sort σ -> Type).

(** Given [A : Carriers σ] and [w : SymbolType σ], the domain of an
    algebra operation [DomOperation A w] is a product of carrier types
    from [A], indexed by [Arity w]. *)

Notation DomOperation A w
  := (forall i : Arity w, A (sorts_dom w i)) (only parsing).

(** Given a symbol type [w : SymbolType σ], an algebra with carriers
    [A : Carriers σ] provides a corresponding operation of type
    [Operation A w]. See below for definition [Algerba].

    Algebra operations are developed further in
    [HoTT.Algebra.Universal.Operation]. *)

Definition Operation {σ} (A : Carriers σ) (w : SymbolType σ) : Type
  := DomOperation A w -> A (sort_cod w).

(** An [Algebra σ] for a signature [σ] consists of a collection of
    carriers [Carriers σ], and for each symbol [u : Symbol σ], an
    operation/function of type [Operation carriers (σ u)],
    where [σ u : SymbolType σ] is the symbol type of [u].
    Notice that [Algebra] does not specify equations involving
    carriers and operations. Equations are defined elsewhere. *)

Record Algebra {σ : Signature} : Type := Build_Algebra
  { carriers : Carriers σ
  ; operations : forall (u : Symbol σ), Operation carriers (σ u)
  ; hset_algebra : forall (s : Sort σ), IsHSet (carriers s) }.

Arguments Algebra : clear implicits.

Arguments Build_Algebra {σ} carriers operations {hset_algebra}.

Global Existing Instance hset_algebra.

Global Coercion carriers : Algebra >-> Funclass.

Bind Scope Algebra_scope with Algebra.

Definition SigAlgebra (σ : Signature) : Type
  := {c : Carriers σ
        | { _ : forall (u : Symbol σ), Operation c (σ u)
              | forall (s : Sort σ), IsHSet (c s) } }.

Lemma issig_algebra (σ : Signature) : SigAlgebra σ <~> Algebra σ.
Proof.
  issig.
Defined.

Lemma path_algebra `{Funext} {σ : Signature} (A B : Algebra σ)
  (p : carriers A = carriers B)
  (q : transport (fun i => forall u, Operation i (σ u)) p (operations A)
       = operations B)
  : A = B.
Proof.
  apply (ap (issig_algebra σ)^-1)^-1; cbn.
  apply (path_sigma' _ p).
  refine (transport_sigma p _ @ _).
  apply path_sigma_hprop.
  exact q.
Defined.

Arguments path_algebra {_} {_} (A B)%_Algebra_scope (p q)%_path_scope.

Lemma path_ap_carriers_path_algebra `{Funext} {σ} (A B : Algebra σ)
  (p : carriers A = carriers B)
  (q : transport (fun i => forall u, Operation i (σ u)) p (operations A)
       = operations B)
  : ap carriers (path_algebra A B p q) = p.
Proof.
  destruct A as [A a ha], B as [B b hb]; cbn in p, q.
  destruct p, q.
  unfold path_algebra, path_sigma_hprop, path_sigma_uncurried.
  cbn -[center].
  by destruct (center (ha = hb)).
Defined.

Arguments path_ap_carriers_path_algebra {_} {_} (A B)%_Algebra_scope (p q)%_path_scope.

Lemma path_path_algebra_issig {σ : Signature} {A B : Algebra σ} (p q : A = B)
  (r : ap (issig_algebra σ)^-1 p = ap (issig_algebra σ)^-1 q)
  : p = q.
Proof.
  set (e := (equiv_ap (issig_algebra σ)^-1 A B)).
  by apply (@equiv_inv _ _ (ap e) (Equivalences.isequiv_ap _ _)).
Defined.

Arguments path_path_algebra_issig {_} {A B}%_Algebra_scope (p q r)%_path_scope.

Lemma path_path_algebra `{Funext} {σ} {A B : Algebra σ}
  (p q : A = B) (r : ap carriers p = ap carriers q)
  : p = q.
Proof.
  apply path_path_algebra_issig.
  unshelve eapply path_path_sigma.
  - transitivity (ap carriers p); [by destruct p |].
    transitivity (ap carriers q); [exact r | by destruct q].
  - apply path_ishprop.
Defined.

Arguments path_path_algebra {_} {σ} {A B}%_Algebra_scope (p q r)%_path_scope.

Global Notation "u .# A" := (operations A u) : Algebra_scope.
