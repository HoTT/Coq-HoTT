(* -*- mode: coq; mode: visual-line -*- *)
(** * Pointed Types *)

Require Import Overture.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
Generalizable Variables A B f.

(** Any contratible type is pointed. *)
Instance ispointed_contr `{Contr A} : IsPointed A := center A.

(** A pi type with a pointed target is pointed. *)
(** I'm not sure why I need to explicitly pass the instance to [point] here. -Jason Gross *)
Instance ispointed_forall `{H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a)
  := fun a => @point (B a) (H a).

(** A sigma type of pointed components is pointed. *)
Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A cartesian product of pointed types is pointed. *)
Instance ispointed_pord `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(** The type [x = x] is pointed. *)
Instance ispointed_loop_space A (a : A) : IsPointed (a = a) := idpath.
