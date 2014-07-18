(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*   This file has been modified for the purposes of the HoTT library.  *)
(************************************************************************)

Require Import Notations.

Ltac easy :=
  let rec use_hyp H :=
    match type of H with
    | _ => try solve [inversion H]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : _ |- _ => solve [inversion H]
    | _ => idtac
    end in
  let rec do_atom :=
    solve [reflexivity | symmetry; trivial] ||
    contradiction ||
    (split; do_atom)
  with do_ccl := trivial; repeat do_intro; do_atom in
  (use_hyps; do_ccl) || fail "Cannot solve this goal".

Tactic Notation "now" tactic(t) := t; easy.
