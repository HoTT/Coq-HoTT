(* -*- mode: coq; mode: visual-line -*- *)
(** Contractibility *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Naming convention: we consistently abbreviate "contractible" as "contr".  A theorem about a space [X] being contractible (which will usually be an instance of the typeclass [Contr]) is called [contr_X]. *)

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
Generalizable Variables A B f.

(** If a space is contractible, then any two points in it are connected by a path in a canonical way. *)
Definition path_contr `{Contr A} (x y : A) : x = y
  := (contr x)^ @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; apply symmetry; now apply concat_Vp.
  path_via (path_contr x y).
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)
Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) := {
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
}.

(** Also, the total space of any based path space is contractible. *)
Instance contr_basedpaths {X : Type} (x : X) : Contr {y : X & x = y}.
  exists (x ; 1).
  intros [y []]; reflexivity.
Defined.

Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x}.
  exists (existT (fun y => y = x) x 1).
  intros [y []]; reflexivity.
Defined.
