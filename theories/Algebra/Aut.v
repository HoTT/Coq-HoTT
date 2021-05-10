(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import Truncations.
Require Import Algebra.ooGroup.
Require Import Spaces.BAut.

(** * Automorphism oo-Groups *)

(** We define [Aut X] using the pointed, connected type [BAut X]. *)
Definition Aut (X : Type) : ooGroup
  := Build_ooGroup (Build_pType (BAut X) _) _.
