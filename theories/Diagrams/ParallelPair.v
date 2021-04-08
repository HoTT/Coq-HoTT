Require Import HoTT.Basics.
Require Import HoTT.Types.
Require Import HoTT.Diagrams.Graph.
Require Import HoTT.Diagrams.Diagram.
Require Import HoTT.Diagrams.Cocone.

(** Parallel pairs *)

Definition parallel_pair_graph : Graph.
Proof.
  srapply (Build_Graph Bool).
  intros i j.
  exact (if i then if j then Empty else Bool else Empty).
Defined.

(** Parallel pair diagram *)

Definition parallel_pair {A B : Type} (f g : A -> B)
  : Diagram parallel_pair_graph.
Proof.
  srapply Build_Diagram.
  1: intros []; [exact A | exact B].
  intros [] [] []; [exact f | exact g].
Defined.

(** Cones on [parallel_pair]s *)

Definition Build_parallel_pair_cocone {A B Q} {f g : B -> A}
  `(q: A -> Q) (Hq: q o g == q o f)
  : Cocone (parallel_pair f g) Q.
Proof.
  srapply Build_Cocone.
  1: intros []; [exact (q o f) | exact q].
  intros [] [] []; [reflexivity | exact Hq].
Defined.