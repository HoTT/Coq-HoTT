(** * H-Set *)

Require Import Overture Contractible Equivalences Trunc HProp types.Paths.
Local Open Scope equiv_scope.

(** ** Facts about [HSet] *)

(** A type is a set if and only if it satisfies Axiom K. *)

(*
Definition axiomK A := forall (x : A) (p : x = x), p = idpath x.

Definition isset_implies_axiomK A : is_hset A -> axiomK A.
Proof.
  intros H x p.
  apply (H x x p (idpath x)).
Defined.

Definition axiomK_implies_isset A : axiomK A -> is_hset A.
Proof.
  intros H x y.
  apply allpath_prop.
  intros p q.
  induction q.
  apply H.
Defined.

Theorem isset_equiv_axiomK {A} :
  is_hset A <~> (forall (x : A) (p : x = x), p = idpath x).
Proof.
  apply (equiv_from_hequiv (isset_implies_axiomK A) (axiomK_implies_isset A)).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro p.
  apply contr_path.
  apply (axiomK_implies_isset A H).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply prop_path.
  apply isprop_isprop.
Defined.

Definition isset_isprop A : is_prop (is_hset A) := hlevel_isprop 2 A.

Theorem axiomK_isprop A : is_prop (axiomK A).
Proof.
  apply @hlevel_equiv with (A := is_hset A).
  apply isset_equiv_axiomK.
  apply hlevel_isprop.
Defined.

Theorem set_path2 (A : Type) (x y : A) (p q : x = y) :
  is_hset A -> (p = q).
Proof.
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
  K x (idpath x) = idpath (idpath x).
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
  forall (x y : A), (x = y) + ((x = y) -> Empty).

(* Usually this lemma would be proved with [discriminate], but
   unfortunately that tactic is hardcoded to work only with Coq's
   [Prop]-valued equality. *)
Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y :=
  transport (P := fun (s : A + B) => x = (match s with inl a => a | inr b => x end)) p (idpath x).

Theorem decidable_implies_axiomK {A : Type} : decidable_paths A -> axiomK A.
Proof.
  intro d.
  intros x p.
  set (qp := map_dep (d x) p).
  set (q := d x x) in *.
  clearbody qp; revert qp.
  destruct q as [q | q'].
  intro qp0. 
  apply (concat_cancel_left q).
  path_via (transport p q).
  apply opposite, trans_is_concat.
  path_via q.
  set (qp1 := trans_map p (fun y => @inl (x = y) (x = y -> Empty)) q).
  simpl in qp1.
  apply @inl_injective with (B := (x = x -> Empty)).
  exact (qp1 @ qp0).
  induction (q' p).
Defined.

Corollary decidable_isset (A : Type) : decidable_paths A -> is_hset A.
Proof.
  intro.
  apply axiomK_implies_isset, decidable_implies_axiomK.
  assumption.
Defined.

*)