From HoTT Require Import Basics.
Require Import Truncations.
Require Import Algebra.ooGroup.
Require Import Universes.BAut.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(** * Automorphism oo-Groups *)

(** We define [Aut X] using the pointed, connected type [BAut X]. *)
Definition Aut (X : Type) : ooGroup
  := Build_ooGroup [BAut X, _] _.
