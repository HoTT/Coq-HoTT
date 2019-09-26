Require Import Basics.
Require Import Types.

(** * Graphs *)

(** A [Graph] is a type [graph0] of points together with a type [graph1] of arrows between each points. *)

Record Graph := {
  graph0 : Type;
  graph1 : graph0 -> graph0 -> Type;
}.

Coercion graph0 : Graph >-> Sortclass.
Coercion graph1 : Graph >-> Funclass.
