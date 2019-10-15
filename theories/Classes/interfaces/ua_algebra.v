(** This file defines [Algebra]. *)

Require Export
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Basics.Trunc
  HoTT.Classes.implementations.ne_list
  HoTT.Classes.implementations.family_prod.

Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.Types.Arrow
  HoTT.Types.Forall
  HoTT.Types.Universe
  HoTT.HSet
  HoTT.Classes.implementations.list.

Import ne_list.notations.

Declare Scope Algebra_scope.

Delimit Scope Algebra_scope with Algebra.

Open Scope Algebra_scope.

Definition SymbolType_internal : Type → Type := ne_list.

(** A [Signature] is used to characterise [Algebra]s. In particular
    a signature specifies which operations (functions) an algebra for
    the signature is expected to provide. A signature consists of
    - A type of [Sort]s. An algebra for the signature must provide
      a type for each [s : Sort].
    - A type of function symbols [Symbol]. For each function symbol
      [u : Symbol], an algebra for the signature must provide a
      corresponding operation.
    - The field [symbol_types σ u] indicates which type the operation
      corresponding to [u] should have. *)

Record Signature : Type := BuildSignature
  { Sort : Type
  ; Symbol : Type
  ; symbol_types : Symbol → SymbolType_internal Sort }.

(** We have this implicit coercion allowing us to use a signature
    [σ:Signature] as a map [Symbol σ → SymbolType σ]
    (see [SymbolType] below). *)

Global Coercion symbol_types : Signature >-> Funclass.

(** A single sorted [Signature] is a signature with [Sort = Unit]. *)

Definition BuildSingleSortedSignature (sym : Type) (arities : sym → nat)
  : Signature
  := BuildSignature Unit sym (ne_list.replicate_Sn tt o arities).

(** Let [σ:Signature]. For each symbol [u : Symbol σ], [σ u]
    associates [u] to a [SymbolType σ]. This represents the required
    type of the algebra operation corresponding to [u]. *)

Definition SymbolType (σ : Signature) : Type := ne_list (Sort σ).

(** For [s : SymbolType σ], [cod_symboltype σ] is the codomain of the
    symbol type [s]. *)

Definition cod_symboltype {σ} : SymbolType σ → Sort σ
  := ne_list.last.

(** For [s : SymbolType σ], [cod_symboltype σ] is the domain of the
    symbol type [s]. *)

Definition dom_symboltype {σ} : SymbolType σ → list (Sort σ)
  := ne_list.front.

(** For [s : SymbolType σ], [cod_symboltype σ] is the arity of the
    symbol type [s]. That is the number [n:nat] of arguments of the
    [SymbolType σ]. *)

Definition arity_symboltype {σ} : SymbolType σ → nat
  := length o dom_symboltype.

(** An [Algebra] must provide a family of [Carriers σ] indexed by
    [Sort σ]. These carriers are the "objects" (types) of the algebra. *)

(* [Carriers] is a notation because it will be used for an implicit
   coercion [Algebra >-> Funclass] below. *)

Notation Carriers σ := (Sort σ → Type).

(** The function [Operation] maps a family of carriers [A : Carriers σ]
    and [w : SymbolType σ] to the corresponding function type.

    <<
      Operation A [:s1; s2; ...; sn; t:] = A s1 → A s2 → ... → A sn → A t
    >>

    where [[:s1; s2; ...; sn; t:] : SymbolType σ] is a symbol type
    with domain [[s1; s2; ...; sn]] and codomain [t]. *)

Fixpoint Operation {σ} (A : Carriers σ) (w : SymbolType σ) : Type
  := match w with
     | [:s:] => A s
     | s ::: w' => A s → Operation A w'
     end.

Global Instance trunc_operation `{Funext} {σ : Signature}
  (A : Carriers σ) {n} `{!∀ s, IsTrunc n (A s)} (w : SymbolType σ)
  : IsTrunc n (Operation A w).
Proof.
  induction w; apply (istrunc_trunctype_type (BuildTruncType n _)).
Defined.

(** Uncurry of an [f : Operation A w], such that

    <<
      ap_operation f (x1,x2,...,xn) = f x1 x2 ... xn
    >>
*)

Fixpoint ap_operation {σ} {A : Carriers σ} {w : SymbolType σ}
    : Operation A w →
      FamilyProd A (dom_symboltype w) →
      A (cod_symboltype w)
    := match w with
       | [:s:] => λ f _, f
       | s ::: w' => λ f '(x, l), ap_operation (f x) l
       end.

(** Funext for uncurried [Operation A w]. If

    <<
      ap_operation f (x1,x2,...,xn) = ap_operation g (x1,x2,...,xn)
    >>

    for all [(x1,x2,...,xn) : A s1 * A s2 * ... * A sn], then [f = g]. *)

Fixpoint path_forall_ap_operation `{Funext} {σ : Signature}
  {A : Carriers σ} {w : SymbolType σ}
  : ∀ (f g : Operation A w),
    (∀ a : FamilyProd A (dom_symboltype w),
       ap_operation f a = ap_operation g a)
    -> f = g
  := match w with
     | [:s:] => λ (f g : A s) p, p tt
     | s ::: w' =>
         λ (f g : A s → Operation A w') p,
          path_forall f g
            (λ x, path_forall_ap_operation (f x) (g x) (λ a, p (x,a)))
     end.

(** An [Algebra σ] for a signature [σ] consists of a family [carriers :
    Carriers σ] indexed by the sorts [s : Sort σ], and for each symbol
    [u : Symbol σ], an operation of type [Operation carriers (σ u)],
    where [σ u : SymbolType σ] is the symbol type of [u]. *)

Record Algebra {σ : Signature} : Type := BuildAlgebra
  { carriers : Carriers σ
  ; operations : ∀ (u : Symbol σ), Operation carriers (σ u) }.

Arguments Algebra : clear implicits.

Arguments BuildAlgebra {σ} carriers operations.

(** We have a convenient implicit coercion from an algebra to the
    family of carriers. *)
Global Coercion carriers : Algebra >-> Funclass.

Definition SigAlgebra (σ : Signature) : Type
  := {c : Carriers σ | ∀ (u : Symbol σ), Operation c (σ u) }.

Lemma issig_algebra (σ : Signature) : SigAlgebra σ <~> Algebra σ.
Proof.
  unfold SigAlgebra.
  issig (@BuildAlgebra σ) (@carriers σ) (@operations σ).
Defined.

Class IsTruncAlgebra (n : trunc_index) {σ : Signature} (A : Algebra σ)
  := trunc_carriers_algebra : ∀ (s : Sort σ), IsTrunc n (A s).

Global Existing Instance trunc_carriers_algebra.

Notation IsHSetAlgebra := (IsTruncAlgebra 0).

Global Instance hprop_is_trunc_algebra `{Funext} (n : trunc_index)
  {σ : Signature} (A : Algebra σ)
  : IsHProp (IsTruncAlgebra n A).
Proof.
  apply trunc_forall.
Qed.

Global Instance trunc_algebra_succ {σ : Signature} (A : Algebra σ)
  {n} `{!IsTruncAlgebra n A}
  : IsTruncAlgebra n.+1 A | 1000.
Proof.
  intro; exact _.
Qed.

(** To find a path between two algebras [A B : Algebra σ] it suffices
    to find paths between the carriers and the operations. *)

Lemma path_algebra {σ : Signature} (A B : Algebra σ)
  (p : carriers A = carriers B)
  (q : transport (λ X, ∀ u, Operation X (σ u)) p (operations A)
       = operations B)
  : A = B.
Proof.
  destruct A,B. cbn in *. by path_induction.
Defined.

Lemma path_ap_carriers_path_algebra {σ} (A B : Algebra σ)
  (p : carriers A = carriers B)
  (q : transport (λ X, ∀ u, Operation X (σ u)) p (operations A)
       = operations B)
  : ap carriers (path_algebra A B p q) = p.
Proof.
  destruct A as [A a], B as [B b]. cbn in *. by destruct p,q.
Defined.

(** Suppose [p],[q] are paths in [Algebra σ]. To show that [p = q] it
    suffices to find a path [r] between the paths corresponding to
    [p] and [q] in [SigAlgebra σ]. *)

Lemma path_path_algebra {σ : Signature} {A B : Algebra σ} (p q : A = B)
  (r : ap (issig_algebra σ)^-1 p = ap (issig_algebra σ)^-1 q)
  : p = q.
Proof.
  set (e := (Paths.equiv_ap (issig_algebra σ)^-1 A B)).
  by apply (@equiv_inv _ _ (ap e) (Equivalences.isequiv_ap _ _)).
Defined.

(** If [p q : A = B] and [IsHSetAlgebra B].
    Then [ap carriers p = ap carriers q] implies [p = q]. *)

Lemma path_path_hset_algebra `{Funext} {σ : Signature}
  {A B : Algebra σ} `{IsHSetAlgebra B}
  (p q : A = B) (r : ap carriers p = ap carriers q)
  : p = q.
Proof.
  apply path_path_algebra.
  unshelve eapply path_path_sigma.
  - transitivity (ap carriers p); [by destruct p |].
    transitivity (ap carriers q); [exact r | by destruct q].
  - apply hprop_allpath. apply hset_path2.
Defined.

Module algebra_notations.

(** Given [A : Algebra σ] and function symbol [u : Symbol σ], we use
    the notation [u ^^ A] to refer to the corresponding algebra
    operation of type [Operation A (σ u)]. *)

  Global Notation "u ^^ A" := (operations A u)
                              (at level 60, no associativity)
                              : Algebra_scope.

End algebra_notations.
