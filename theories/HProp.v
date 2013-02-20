(** * HPropositions *)

Require Import Overture Contractible Equivalences Trunc.
Require Import types.Forall types.Sigma types.Record.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** ** Facts about [IsHProp] *)

(** Maybe this should go to a separate file? *)

Generalizable Variables A B.

(** An inhabited proposition is contractible.
   This is not an [Instance] because it causes infinite loops.
   *)
Lemma Contr_inhabited_HProp (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  simpl in H.
  apply center, H.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition. *)
Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A.
Proof.
  intro H.
  intros x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** If a type is contractible, then so is its type of contractions.
    Using [issig_contr] and the [equiv_intro] tactic, we can transfer this to the equivalent problem of contractibility of a certain Sigma-type, in which case we can apply the general path-construction functions. *)
Instance contr_contr `{Funext} (A : Type)
  : Contr A -> Contr (Contr A).
Proof.
  intros c; exists c; generalize c.
  equiv_intro (issig_contr A) c'.
  equiv_intro (issig_contr A) d'.
  refine (ap _ _).
  refine (path_sigma _ _ _ ((contr (c'.1))^ @ contr (d'.1)) _).
  refine (path_forall _ _ _); intros x.
  apply path2_contr.
Qed.

(** This provides the base case in a proof that truncatedness is a proposition. *)
Instance hprop_trunc `{Funext} (n : trunc_index) (A : Type)
  : IsHProp (IsTrunc n A).
Proof.
  apply hprop_inhabited_contr.
  revert A.
  induction n as [| n I]; unfold IsTrunc; simpl.
  - intros A ?.
    exact _.
  - intros A AH1.
    exists AH1.
    intro AH2.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply @path_contr.
    apply I, AH1.
Qed.

(** Chracterization of [IsHProp] in terms of all points being connected by paths. *)

Theorem allpath_HProp `{H : IsHProp A} : forall x y : A, x = y.
Proof.
  intros x y.
  apply H.
Defined.

Theorem HProp_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.

Theorem Equiv_HProp_allpath `{Funext} (A : Type)
  : IsHProp A <~> (forall (x y : A), x = y).
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

Definition equiv_iff_prop `{IsHProp A} `{IsHProp B}
  : (A -> B) -> (B -> A) -> (A <~> B).
Proof.
  intros f g.
  apply (equiv_adjointify f g);
    intros ?; apply allpath_HProp.
Defined.


(** [IsHProp] is closed under [forall].  This should really be a theorem in types/Forall that all truncation levels are closed under [forall]. *)
  
Instance hprop_forall `{E : Funext} (A : Type) (P : A -> Type) :
  (forall x, IsHProp (P x)) -> IsHProp (forall x, P x).
Proof.
  intro.
  apply HProp_allpath.
  intros f g.
  apply path_forall; intro.
  apply allpath_HProp.
Defined.


(* Being a contractible space is a proposition. *)

Instance hprop_contr `{Funext} (A : Type) : IsHProp (Contr A).
Proof.
  apply hprop_inhabited_contr.
  intro cA.
  exact _.
Defined.




(** Being an equivalence is a prop. *)
(* Should we need the record tactics?
Instance hprop_isequiv (X Y : Type) (f: X -> Y) : IsHProp (IsEquiv f).
Proof. 
  apply hprop_forall. intros y.
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

