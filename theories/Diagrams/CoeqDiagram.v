Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.

(** The shape of a coequalizer diagram. *)

Definition coequalizer_graph : Graph.
Proof.
  serapply (Build_Graph Bool).
  intros i j.
  exact (if i then if j then Empty else Bool else Empty).
Defined.

(** The coequalizer diagram of two maps. *)

Definition coequalizer_diagram {A B : Type} (f g : A -> B)
  : Diagram coequalizer_graph.
Proof.
  serapply Build_Diagram.
  1: intros []; [exact A | exact B].
  intros [] [] []; [exact f | exact g].
Defined.