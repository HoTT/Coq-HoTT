Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.Cocone.

(** Parallel pairs *)

Definition parallel_pair_graph : Graph.
Proof.
  serapply (Build_Graph Bool).
  intros i j.
  exact (if i then if j then Empty else Bool else Empty).
Defined.

(** Parallel pair diagram *)

Definition parallel_pair {A B : Type} (f g : A -> B)
  : Diagram parallel_pair_graph.
Proof.
  serapply Build_Diagram.
  1: intros []; [exact A | exact B].
  intros [] [] []; [exact f | exact g].
Defined.

(** Cones on [parallel_pair]s *)

Definition Build_parallel_pair_cocone {A B Q} {f g : B -> A}
  `(q: A -> Q) (Hq: q o g == q o f)
  : Cocone (parallel_pair f g) Q.
Proof.
  serapply Build_Cocone.
  1: intros []; [exact (q o f) | exact q].
  intros [] [] []; [reflexivity | exact Hq].
Defined.