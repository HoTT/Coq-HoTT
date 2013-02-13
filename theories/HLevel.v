 (** * H-Levels *)

Require Import Overture Contractible Equivalences types.Paths FunextVarieties.
Local Open Scope equiv_scope.

Generalizable Variable A.

(** A contractible space has h-level zero, of course. *)
Instance Contr_hlevel_0 (A : Type) : is_hlevel 0 A -> Contr A
  := idmap.
  
(** H-levels are cummulative. *)
Lemma hlevel_succ (n : nat) :
  forall A : Type, is_hlevel n A -> is_hlevel (S n) A.
Proof.
  induction n as [| n I].
  - intros A H x y.
    unfold is_hlevel in H.
    apply contr_paths_contr.
  - intros A H x y p q.
    apply I.
    apply H.
Qed.

(** Equivalence preserves h-levels (this is, of course, trivial with univalence). *)
Theorem hlevel_equiv (n : nat) : forall (A B : Type), (A <~> B) -> is_hlevel n A -> is_hlevel n B.
Proof.
  induction n as [| n I].
  - apply Contr_equiv_contr.
  - intros A B e H x y.
    fold is_hlevel.
    apply I with (A := (e^-1 x = e^-1 y)).
    + apply symmetry.
      apply @equiv_ap.
      apply @isequiv_inverse.
    + apply H.
Qed.

Instance prop_inhabited_contr `{HProp A} : A -> Contr A.
Proof.
  intros x.
  exists x.
  intro y.
  apply H.
Defined.

Instance inhabited_contr_isprop {A} : (A -> Contr A) -> HProp A.
Proof.
  intros H. exists. intros x.
  apply (@contr_paths_contr _ (H x)).
Defined.

(* Why is this missing ? *)

Definition Funext_implies_WeakFunext:Funext -> WeakFunext:=
  (fun E=> (NaiveFunext_implies_WeakFunext (Funext_implies_NaiveFunext E))).

Theorem hlevel_inhabited_contr `{E : Funext} {n X} : is_hlevel n X -> Contr (is_hlevel n X).
Proof.
  revert X. induction n.
    intros X H. apply (@contr_Contr _ _ H).
  simpl.
  intros X H. set (wfunext:=(Funext_implies_WeakFunext E)).
  do 2 (apply wfunext; intro).
  by apply IHn.
Defined.

Instance hlevel_isprop `{E : Funext} {n A} : HProp (is_hlevel n A).
Proof.
  exists.
  apply inhabited_contr_isprop.
  apply hlevel_inhabited_contr.
Defined.