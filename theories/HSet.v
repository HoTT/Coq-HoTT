(* -*- mode: coq; mode: visual-line -*-  *)
(** * H-Sets *)

Require Import Overture PathGroupoids Contractible Equivalences Trunc HProp.
Require Import types.Paths types.Sigma types.Empty types.Record.
Require Import FunextVarieties.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** A type is a set if and only if it satisfies Axiom K. *)

Definition axiomK A := forall (x : A) (p : x = x), p = idpath x.

Definition axiomK_hset {A} : IsHSet A -> axiomK A.
Proof.
  intros H x p.
  apply (H x x p (idpath x)).
Defined.

Definition hset_axiomK {A} `{axiomK A} : IsHSet A.
Proof.
  intros x y H.
  apply @hprop_allpath.
  intros p q.
  by induction p.
Defined.

Section AssumeFunext.
Context `{Funext}.

Theorem equiv_hset_axiomK {A} : IsHSet A <~> axiomK A.
Proof.
  apply (equiv_adjointify (@axiomK_hset A) (@hset_axiomK A)).
  - intros K. by_extensionality x. by_extensionality x'.
    cut (Contr (x=x)). intro. eapply path_contr.
    exists 1. intros. apply symmetry, K.
  - intro K. by_extensionality x. by_extensionality x'.
    eapply allpath_hprop.
Defined.

Global Instance axiomK_isprop A : IsHProp (axiomK A) | 0.
Proof.
  apply (trunc_equiv equiv_hset_axiomK).
Defined.

Theorem set_path2 {A} `{IsHSet A} {x y : A} (p q : x = y):
  p = q.
Proof.
  induction q.
  apply axiomK_hset; assumption.
Defined.

(** Recall that axiom K says that any self-path is homotopic to the
   identity path.  In particular, the identity path is homotopic to
   itself.  The following lemma says that the endo-homotopy of the
   identity path thus specified is in fact (homotopic to) its identity
   homotopy (whew!).  *)
(* TODO: What was the purpose of this lemma?  Do we need it at all?  It's actually fairly trivial. *)
Lemma axiomK_idpath {A} (x : A) (K : axiomK A) :
  K x (idpath x) = idpath (idpath x).
Proof.
  pose (T1A := @trunc_succ _ A (@hset_axiomK A K)).
  exact (@set_path2 (x=x) (T1A x x) _ _ _ _).
Defined.

(** Hedberg's theorem: any type with "decidable equality" is a set. *)

Definition decidable_paths (A : Type) :=
  forall (x y : A), (x = y) + (~ (x = y)).

(* Usually this lemma would be proved with [discriminate], but unfortunately that tactic is hardcoded to work only with Coq's [Prop]-valued equality.
   TODO: This should be in types/Sum. *)
Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y :=
  (@transport _ (fun (s : A + B) => x = (match s with inl a => a | inr b => x end)) _ _ p (idpath x)).

Theorem axiomK_decidable {A : Type} : @decidable_paths A -> @axiomK A.
Proof.
  intro d.
  intros x p.
  set (qp := apD (d x) p).
  set (q := d x x) in *.
  clearbody qp; revert qp.
  destruct q as [q | q'].
    intro qp0; apply (cancelL q). path_via (transport _ p q).
      symmetry; apply transport_paths_r.
      path_via q. apply @inl_injective with (B := (~ x = x)).
      exact ((ap_transport p (fun y => @inl (x = y) (~x = y)) q) @ qp0).
  induction (q' p).
Defined.

Corollary hset_decidable {A : Type} : @decidable_paths A -> IsHSet A.
Proof.
  intro.
  by apply @hset_axiomK, @axiomK_decidable.
Defined.

End AssumeFunext.

Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
(** This one is needed in epi_surj to coerce hProp into hSet*)
Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
Hint Resolve iss.
Global Existing Instance iss.