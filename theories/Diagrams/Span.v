Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.

(** The underlying graph of a span. *)

Definition span_graph : Graph.
Proof.
  serapply (Build_Graph (Unit + Bool)).
  intros [i|i] [j|j].
  2: exact Unit.
  all: exact Empty.
Defined.

Section Span.

  Context {A B C : Type}.

  (** A span is a diagram:
         f     g
      B <-- A --> C     *)

  Definition span (f : A -> B) (g : A -> C) : Diagram span_graph.
  Proof.
    serapply Build_Diagram.
    - intros [i|i].
      + exact A.
      + exact (if i then B else C).
    - intros [i|i] [j|j] u; cbn; try contradiction.
      destruct j.
      + exact f.
      + exact g.
  Defined.

End Span.