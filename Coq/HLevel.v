Require Import Paths Fibrations Contractible Equivalences Funext.
Require Import UnivalenceAxiom.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** Some more stuff about contractibility. *)

Theorem contr_contr {X} : is_contr X -> is_contr (is_contr X).
  intros X ctr1.
  exists ctr1. intros ctr2.
  apply @total_path with (p := pr2 ctr1 (pr1 ctr2)).
  apply funext_dep.
  intro x.
  apply contr_path2.
  assumption.
Defined.

(** H-levels. *)

Fixpoint is_hlevel (n : nat) : Type -> Type :=
  match n with
    | 0 => is_contr
    | S n' => fun X => forall (x y:X), is_hlevel n' (x ~~> y)
  end.

Theorem hlevel_inhabited_contr {n X} : is_hlevel n X -> is_contr (is_hlevel n X).
Proof.
  intros n.
  induction n.
  intro X.
  apply contr_contr.
  intro X.
  simpl.
  intro H.
  apply weak_funext.
  intro x.
  apply weak_funext.
  intro y.
  apply IHn.
  apply H.
Defined.

(** H-level is preserved under equivalence. *)

Theorem hlevel_equiv {n A B} : (A ≃> B) -> is_hlevel n A -> is_hlevel n B.
Proof.
  intro n.
  induction n.
  simpl.
  apply @contr_equiv_contr.
  simpl.
  intros A B f H x y.
  apply IHn with (A := f (f⁻¹ x) ~~> y).
  apply concat_equiv_left.
  apply opposite, inverse_is_section.
  apply IHn with (A := f (f⁻¹ x) ~~> f (f⁻¹ y)).
  apply concat_equiv_right.
  apply inverse_is_section.
  apply IHn with (A := (f⁻¹ x) ~~> (f⁻¹ y)).
  apply equiv_map_equiv.
  apply H.
Defined.

(** Propositions are of h-level 1. *)

Definition is_prop := is_hlevel 1.

(** Here is an alternate characterization of propositions. *)

Theorem prop_inhabited_contr {A} : is_prop A -> A -> is_contr A.
Proof.
  intros A H x.
  exists x.
  intro y.
  apply H.
Defined.

Theorem inhabited_contr_isprop {A} : (A -> is_contr A) -> is_prop A.
Proof.
  intros A H x y.
  apply contr_pathcontr.
  apply H.
  assumption.
Defined.

Theorem hlevel_isprop {n A} : is_prop (is_hlevel n A).
Proof.
  intros n A.
  apply inhabited_contr_isprop.
  apply hlevel_inhabited_contr.
Defined.

Definition isprop_isprop {A} : is_prop (is_prop A) := hlevel_isprop.

Theorem prop_equiv_inhabited_contr {A} : is_prop A ≃> (A -> is_contr A).
Proof.
  intros A.
  exists prop_inhabited_contr.
  apply hequiv_is_equiv with (g := inhabited_contr_isprop).
  intro H.
  unfold prop_inhabited_contr, inhabited_contr_isprop.
  simpl.
  apply funext.
  intro x.
  apply contr_path.
  apply contr_contr.
  exact (H x).
  intro H.
  unfold prop_inhabited_contr, inhabited_contr_isprop.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply contr_contr.
  exact (H x y).
Defined.

(** And another one. *)

Theorem prop_path {A} : is_prop A -> forall (x y : A), x ~~> y.
Proof.
  intro A.
  unfold is_prop. simpl.
  intros H x y.
  exact (pr1 (H x y)).
Defined.

Theorem allpath_prop {A} : (forall (x y : A), x ~~> y) -> is_prop A.
  intro A.
  intros H x y.
  assert (K : is_contr A).
  exists x. intro y'. apply H.
  apply contr_pathcontr. assumption.
Defined.

Theorem prop_equiv_allpath {A} : is_prop A ≃> (forall (x y : A), x ~~> y).
Proof.
  intro A.
  exists prop_path.
  apply @hequiv_is_equiv with (g := allpath_prop).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply (allpath_prop H).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply contr_contr.
  apply H.
Defined.
  
(** Sets are of h-level 2. *)

Definition is_set := is_hlevel 2.

(** A type is a set if and only if it satisfies Axiom K. *)

Definition axiomK A := forall (x : A) (p : x ~~> x), p ~~> idpath x.

Definition isset_implies_axiomK {A} : is_set A -> axiomK A.
Proof.
  intros A H x p.
  apply H.
Defined.

Definition axiomK_implies_isset {A} : axiomK A -> is_set A.
Proof.
  intros A H x y.
  apply allpath_prop.
  intros p q.
  induction q.
  apply H.
Defined.

Theorem isset_equiv_axiomK {A} :
  is_set A ≃> (forall (x : A) (p : x ~~> x), p ~~> idpath x).
Proof.
  intro A.
  exists isset_implies_axiomK.
  apply @hequiv_is_equiv with (g := axiomK_implies_isset).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro p.
  apply contr_path.
  apply (axiomK_implies_isset H).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply prop_path.
  apply isprop_isprop.
Defined.

Definition isset_isprop {A} : is_prop (is_set A) := hlevel_isprop.

Theorem axiomK_isprop {A} : is_prop (axiomK A).
Proof.
  intro A.
  apply @hlevel_equiv with (A := is_set A).
  apply isset_equiv_axiomK.
  apply hlevel_isprop.
Defined.

Theorem set_path2 (A : Type) (x y : A) (p q : x ~~> y) :
  is_set A -> (p ~~> q).
Proof.
  intros A x y p q.
  intro H.
  apply contr_path.
  apply prop_inhabited_contr.
  cbv. cbv in H.
  apply H.
  assumption.
Defined.

(** Recall that axiom K says that any self-path is homotopic to the
   identity path.  In particular, the identity path is homotopic to
   itself.  The following lemma says that the endo-homotopy of the
   identity path thus specified is in fact (homotopic to) its identity
   homotopy (whew!).  *)

Lemma axiomK_idpath (A : Type) (x : A) (K : axiomK A) :
  K x (idpath x) ~~> idpath (idpath x).
Proof.
  intros.
  set (qq := map_dep (K x) (K x (idpath x))).
  set (q2 := !trans_is_concat_opp (K x (idpath x)) (K x (idpath x)) @ qq).
  path_via (!! K x (idpath x)).
  path_via (! idpath (idpath x)).
  apply concat_cancel_right with (r := K x (idpath x)).
  cancel_units.
Defined.

(** Any type with "decidable equality" is a set. *)

Definition decidable_paths (A : Type) :=
  forall (x y : A), (x ~~> y) + ((x ~~> y) -> Empty_set).

(* Classically, this lemma would be proved with [discriminate], but
   unfortunately that tactic is hardcoded to work only with Coq's
   Prop-valued equality. *)
Definition inl_injective (A B : Type) (x y : A) (p : inl B x ~~> inl B y) : (x ~~> y) :=
  transport (P := fun (s:A+B) => x ~~> match s with inl a => a | inr b => x end) p (idpath x).

Theorem decidable_isset (A : Type) :
  decidable_paths A -> is_set A.
Proof.
  intros A d.
  apply axiomK_implies_isset.
  intros x p.
  set (q := d x x).
  set (qp := map_dep (d x) p).
  fold q in qp.
  generalize qp.
  clear qp.
  destruct q as [q | q'].
  intro qp0.
  apply concat_cancel_left with (p := q).
  path_via (transport p q).
  apply opposite, trans_is_concat.
  path_via q.
  set (qp1 := trans_map p (fun (x0:A) => inl  (x ~~> x0 -> Empty_set)) q).
  apply inl_injective with (B := (x ~~> x -> Empty_set)).
  exact (qp1 @ qp0).
  induction (q' p).
Defined.
