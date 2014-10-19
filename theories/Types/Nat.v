(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers *)

Require Import HoTT.Basics.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.
