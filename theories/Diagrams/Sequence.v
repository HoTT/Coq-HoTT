Require Import Basics.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.

Local Open Scope nat_scope.
Local Open Scope path_scope.

(** * Sequence *)

(** A Sequence is a sequence of maps from [X(n)] to [X(n+1)]. *)

Definition sequence_graph : Graph.
Proof.
  srapply (Build_Graph nat).
  intros n m; exact (S n = m).
Defined.

Definition Sequence := Diagram sequence_graph.

Definition sequence_arr (X : Sequence) (n : nat) : X n -> X n.+1.
Proof.
  snrapply arr.
  exact idpath.
Defined.

Definition Build_Sequence
  (X : nat -> Type)
  (f : forall n, X n -> X n.+1)
  : Sequence.
Proof.
  srapply Build_Diagram.
  1: exact X.
  intros ? ? p.
  destruct p.
  apply f.
Defined.

Definition Build_SequenceMap
  {X Y : Sequence}
  (f : forall n, X n -> Y n)
  (H : forall n, f n.+1 o (sequence_arr X n) == (sequence_arr Y n) o f n)
  : DiagramMap X Y.
Proof.
  snrapply Build_DiagramMap.
  - exact f.
  - intros i j; revert j.
    snrapply paths_ind.
    intros x.
    symmetry.
    apply H.
Defined.

(** A useful lemma to show than two sequences are equivalent. *)

Definition equiv_sequence (D1 D2 : Sequence)
  (H0 : (D1 0) <~> (D2 0))
  (Hn: forall n (e: (D1 n) <~> (D2 n)),
    {e' : (D1 n.+1) <~> (D2 n.+1) & (D2 _f 1) o e == e' o (D1 _f 1)})
  : D1 ~d~ D2.
Proof.
  srapply (Build_diagram_equiv (Build_DiagramMap _ _)); intro n; simpl.
  - apply equiv_fun.
    induction n.
    + apply H0.
    + exact (Hn n IHn).1.
  - intros m q; destruct q.
    induction n; simpl.
    + exact (Hn 0 H0).2.
    + simple refine (Hn n.+1 _).2.
  - induction n; simpl.
    + apply H0.
    + apply (Hn n _ ).1.
Defined.
