Require Import Basics Types Limits.Pullback Colimits.Pushout.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Homotopy.Suspension Homotopy.BlakersMassey.

(** * The Freudenthal Suspension Theorem *)

(** The Freudenthal suspension theorem is a fairly trivial corollary of the Blakers-Massey theorem. *)
Local Definition freudenthal' `{Univalence} (n : trunc_index)
           (X : Type) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (@merid X).
Proof.
  snrapply cancelL_equiv_conn_map.
  - exact (Pullback (pushl (f:=const_tt X) (g:=const_tt X)) pushr).
  - symmetry.
    do 2 refine (_ oE equiv_contr_sigma _).
    reflexivity.
  - rapply blakers_massey_po.
Defined.

Definition freudenthal@{u v | u < v} := Eval unfold freudenthal' in @freudenthal'@{u u v u u u u u u}.

Global Existing Instance freudenthal.
