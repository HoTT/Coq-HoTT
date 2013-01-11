(** * HPropositions *)

Require Import Overture Contractible Equivalences HLevel types.Forall.

(** ** Facts about [HProp] *)

(** Maybe this should go to a separate file? *)

Generalizable Variable A.

(** An inhabited proposition is contractible. *)
Lemma Contr_inhabited_HProp (A : Type) `{H : HProp A} (x : A) : Contr A.
Proof.
  exists x.
  intro y.  
  destruct H as [i].
  apply i.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition. *)
Instance HProp_inhabited_Contr (A : Type) : (A -> Contr A) -> HProp A.
Proof.
  intro H.
  exists.
  intros x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** [is_hlevel] is a proposition. *)
Instance HProp_is_hlevel `{E : Funext} (n  : nat) (A : Type) : HProp (is_hlevel n A).
Proof.
  apply HProp_inhabited_Contr.
  generalize A; clear A.
  induction n as [| n I].
  - intros A H.
    unfold is_hlevel in * |- *.
    apply contr_Contr.
  - intros A H.
    exists H.
    intro G.
    apply path_forall; intro x.
    apply path_forall; intro y.
    simpl in G, H.
    apply @path_contr.
    apply I, H.
Qed.

(* Being a contractible space is a proposition. *)

Instance HProp_Contr `{Funext} (A : Type) : HProp (Contr A).
Proof.
  apply HProp_inhabited_Contr.
  intro cA.
  apply contr_Contr.
Defined.

(** Being an equivalence is a prop. *)

(*
Instance HProp_IsEquiv (X Y : Type) (f: X -> Y) : HProp (IsEquiv f).
Proof.
  apply forall_isprop. intros y.
  apply iscontr_isprop.
Defined.
*)
(*

(** Here is an alternate characterization of propositions. *)

Definition isprop_isprop A : is_prop (is_prop A) := hlevel_isprop 1 A.


Theorem prop_equiv_inhabited_contr {A} : is_prop A <~> (A -> is_contr A).
Proof.
  apply (equiv_from_hequiv (prop_inhabited_contr A) (inhabited_contr_isprop A)).
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

Theorem prop_path {A} : is_prop A -> forall (x y : A), x = y.
Proof.
  unfold is_prop. simpl.
  intros H x y.
  exact (pr1 (H x y)).
Defined.

Theorem allpath_prop {A} : (forall (x y : A), x = y) -> is_prop A.
  intros H x y.
  assert (K : is_contr A).
  exists x. intro y'. apply H.
  apply contr_pathcontr. assumption.
Defined.

Theorem prop_equiv_allpath {A} : is_prop A <~> (forall (x y : A), x = y).
Proof.
  apply (equiv_from_hequiv prop_path allpath_prop).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply (allpath_prop  H).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply contr_contr.
  apply H.
Defined.
  
Instance HProp_forall (A : Type) (P : A -> Type) :
  (forall x, HProp (P x)) -> HProp (forall x, P x).
Proof.
  intros H.
  apply allpath_prop.
  intros f g.
  apply funext_dep. intros x.
  apply prop_path.
  apply H.
Defined.

(** Two propositions are equivalent as soon as there are maps in both
   directions. *)

Definition prop_iff_equiv A B : is_prop A -> is_prop B ->
  (A -> B) -> (B -> A) -> (A <~> B).
Proof.
  intros Ap Bp f g.
  apply (equiv_from_hequiv f g); 
  intros; apply prop_path; auto.
Defined.

*)

