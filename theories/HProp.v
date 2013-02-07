(** * HPropositions *)

Require Import Overture Contractible Equivalences Trunc types.Forall.
Local Open Scope equiv_scope.

(** ** Facts about [HProp] *)

(** Maybe this should go to a separate file? *)

Generalizable Variables A B.

(** An inhabited proposition is contractible.
   This is not an [Instance] because it causes infinite loops.
   *)
Lemma Contr_inhabited_HProp (A : Type) `{H : HProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  simpl in H.
  apply center, H.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition. *)
Instance HProp_inhabited_Contr (A : Type) : (A -> Contr A) -> HProp A.
Proof.
  intro H.
  intros x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** [is_trunc] is a proposition. *)
Instance HProp_is_trunc `{Funext} (n : trunc_index) (A : Type)
  : HProp (Trunc n A).
Proof.
  apply HProp_inhabited_Contr.
  revert A.
  induction n as [| n I]; unfold Trunc; simpl.
  - intros A ?.
    apply contr_Contr.
  - intros A AH1.
    exists AH1.
    intro AH2.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply @path_contr.
    apply I, AH1.
Qed.

(** Chracterization of [HProp] in terms of all points being connected by paths. *)

Theorem allpath_HProp `{H : HProp A} : forall x y : A, x = y.
Proof.
  intros x y.
  apply H.
Defined.

Theorem HProp_allpath (A : Type) : (forall (x y : A), x = y) -> HProp A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.

Theorem Equiv_HProp_allpath `{Funext} (A : Type)
  : HProp A <~> (forall (x y : A), x = y).
Proof.
  apply (equiv_adjointify (@allpath_HProp A) (@HProp_allpath A));
  (* The proofs of the two homotopies making up this equivalence are almost identical.  First we start with a thing [f]. *)
    intro f;
  (* Then we apply funext a couple of times *)
    apply path_forall; intro x;
    apply path_forall; intro y;
  (* Now we conclude that [A] is contractible *)
    try pose (C := BuildContr A x (f x));
    try pose (D := Contr_inhabited_HProp A x);
  (* And conclude because we have a path in a contractible space. *)
    apply path_contr.
Defined.

(** Two propositions are equivalent as soon as there are maps in both
   directions. *)

Definition equiv_iff_prop `{HProp A} `{HProp B}
  : (A -> B) -> (B -> A) -> (A <~> B).
Proof.
  intros f g.
  apply (equiv_adjointify f g);
    intros ?; apply allpath_HProp.
Defined.


(** [HProp] is closed under [forall].  This should really be a theorem in types/Forall that all truncation levels are closed under [forall]. *)
  
Instance HProp_forall `{E : Funext} (A : Type) (P : A -> Type) :
  (forall x, HProp (P x)) -> HProp (forall x, P x).
Proof.
  intro.
  apply HProp_allpath.
  intros f g.
  apply path_forall; intro.
  apply allpath_HProp.
Defined.


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

Definition isprop_isprop A : is_prop (is_prop A) := trunc_isprop 1 A.


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

*)

