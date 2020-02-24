Require Import
  HoTT.Basics
  HoTT.TruncType
  HoTT.HProp
  HoTT.Types
  HoTT.Classes.theory.ua_homomorphism.

Import algebra_notations ne_list.notations.

Section closed_under_op.
  Context `{Funext} {σ} (A : Algebra σ) (P : ∀ s, A s → Type).

  (** Let [α : A s1 → A s2 → ... → A sn → A t] be an algebra
      operation. Then [P] satisfies [ClosedUnderOp α] iff
      for [x1 : A s1], [x2 : A s2], ..., [xn : A sn],

    <<
      P s1 x1 ∧ P s2 x2 ∧ ... ∧ P sn xn
    >>

    implies

    <<
      P t (α x1 x2 ... xn)
    >>
  *)

  Fixpoint ClosedUnderOp {w : SymbolType σ} : Operation A w → Type :=
    match w with
    | [:s:] => P s
    | s ::: w' => λ (α : A s → Operation A w'),
                    ∀ (x : A s), P s x → ClosedUnderOp (α x)
    end.

  Global Instance trunc_closed_under_op {n} `{∀ s x, IsTrunc n (P s x)}
    {w : SymbolType σ} (α : Operation A w)
    : IsTrunc n (ClosedUnderOp α).
  Proof.
    induction w; cbn; exact _.
  Qed.

  Definition IsClosedUnderOps : Type
    := ∀ (u : Symbol σ), ClosedUnderOp (u^^A).

  Global Instance trunc_is_closed_under_ops
    {n} `{∀ s x, IsTrunc n (P s x)}
    : IsTrunc n IsClosedUnderOps.
  Proof.
    apply trunc_forall.
  Qed.
End closed_under_op.

(** [P : ∀ s, A s → Type] is a subalgebra predicate if it is closed
    under operations [IsClosedUnderOps A P] and [P s x] is an h-prop. *)

Section subalgebra_predicate.
  Context  {σ} (A : Algebra σ) (P : ∀ s, A s → Type).

  Class IsSubalgebraPredicate
    := BuildIsSubalgebraPredicate
    { hprop_subalgebra_predicate : ∀ s x, IsHProp (P s x);
      is_closed_under_ops_subalgebra_predicate : IsClosedUnderOps A P }.

  Global Instance hprop_is_subalgebra_predicate `{Funext}
    : IsHProp IsSubalgebraPredicate.
  Proof.
    apply hprop_allpath.
    intros [x1 x2] [y1 y2].
    by destruct (path_ishprop x1 y1), (path_ishprop x2 y2).
  Defined.
End subalgebra_predicate.

Global Arguments BuildIsSubalgebraPredicate {σ A P hprop_subalgebra_predicate}.

Global Existing Instance hprop_subalgebra_predicate.

(** The next section defines subalgebra. *)

Section subalgebra.
  Context
    {σ : Signature} (A : Algebra σ)
    (P : ∀ s, A s → Type) `{!IsSubalgebraPredicate A P}.

(** The subalgebra carriers is the family of subtypes defined by [P]. *)

  Definition carriers_subalgebra : Carriers σ
    := λ (s : Sort σ), {x | P s x}.

(** Let [α : A s1 → ... → A sn → A t] be an operation and let [C :
    ClosedUnderOp A P α]. The corresponding subalgebra operation
    [op_subalgebra α C : (A&P) s1 → ... → (A&P) sn → (A&P) t] is
    given by

    <<
      op_subalgebra α C (x1; p1) ... (xn; pn) =
        (α x1 ... xn; C x1 p1 x2 p2 ... xn pn).
    >>
*)

  Fixpoint op_subalgebra {w : SymbolType σ}
    : ∀ (α : Operation A w),
      ClosedUnderOp A P α → Operation carriers_subalgebra w
    := match w with
       | [:t:] => λ α c, (α; c)
       | s ::: w' => λ α c x, op_subalgebra (α x.1) (c x.1 x.2)
       end.

(** The subalgebra operations [ops_subalgebra] are defined in terms of
    [op_subalgebra]. *)

  Definition ops_subalgebra (u : Symbol σ)
    : Operation carriers_subalgebra (σ u)
    := op_subalgebra (u^^A) (is_closed_under_ops_subalgebra_predicate A P u).

  Definition Subalgebra : Algebra σ
    := BuildAlgebra carriers_subalgebra ops_subalgebra.

  Global Instance trunc_subalgebra {n : trunc_index}
    `{!IsTruncAlgebra n.+1 A}
    : IsTruncAlgebra n.+1 Subalgebra.
  Proof.
    pose proof (hprop_subalgebra_predicate A P).
    intro s. apply @trunc_sigma.
    - exact _.
    - intro. induction n; exact _.
  Qed.
End subalgebra.

Module subalgebra_notations.
  Notation "A & P" := (Subalgebra A P)
                      (at level 50, left associativity)
                      : Algebra_scope.
End subalgebra_notations.

Import subalgebra_notations.

(** The following section defines the inclusion homomorphism
    [Homomorphism (A&P) A], and some related results. *)

Section hom_inc_subalgebra.
  Context
    {σ : Signature} (A : Algebra σ)
    (P : ∀ s, A s → Type) `{!IsSubalgebraPredicate A P}.

  Definition def_inc_subalgebra (s : Sort σ) : (A&P) s → A s
    := pr1.

  Lemma oppreserving_inc_subalgebra {w : SymbolType σ}
    (α : Operation A w) (C : ClosedUnderOp A P α)
    : OpPreserving def_inc_subalgebra (op_subalgebra A P α C) α.
  Proof.
    induction w.
    - reflexivity.
    - intros x. apply IHw.
  Defined.

  Global Instance is_homomorphism_inc_subalgebra
    : IsHomomorphism def_inc_subalgebra.
  Proof.
    intro u. apply oppreserving_inc_subalgebra.
  Defined.

  Definition hom_inc_subalgebra : Homomorphism (A&P) A
    := BuildHomomorphism def_inc_subalgebra.

  Lemma is_isomorphism_inc_improper_subalgebra
    (improper : ∀ s (x : A s), P s x)
    : IsIsomorphism hom_inc_subalgebra.
  Proof.
    intro s.
    refine (isequiv_adjointify _ (λ x, (x; improper s x)) _ _).
    - intro x. reflexivity.
    - intro x. by apply path_sigma_hprop.
  Qed.
End hom_inc_subalgebra.

(** The next section provides paths between subalgebras. These paths
    are convenient to have because the implicit type-class argument
    [IsClosedUnderOps] of [Subalgebra] is complicating things. *)

Section path_subalgebra.
  Context
    {σ : Signature} (A : Algebra σ)
    (P : ∀ s, A s → Type) {CP : IsSubalgebraPredicate A P}
    (Q : ∀ s, A s → Type) {CQ : IsSubalgebraPredicate A Q}.

  Lemma path_subalgebra `{Funext} (p : P = Q) : A&P = A&Q.
  Proof.
    by destruct p, (path_ishprop CP CQ).
  Defined.

  Lemma path_subalgebra_iff `{Univalence} (R : ∀ s x, P s x <-> Q s x)
    : A&P = A&Q.
  Proof.
    apply path_subalgebra.
    funext s x.
    apply (@path_universe _ _ _ (fst (R s x))).
    apply (equiv_equiv_iff_hprop _ _ (R s x)).
  Defined.
End path_subalgebra.
