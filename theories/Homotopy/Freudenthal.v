Require Import Basics Types Limits.Pullback Colimits.Pushout.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Homotopy.Suspension Homotopy.BlakersMassey.

(** * The Freudenthal Suspension Theorem *)

(** The Freudenthal suspension theorem is a fairly trivial corollary of the Blakers-Massey theorem.  It says that [merid : X -> North = South] is highly connected. *)
Global Instance freudenthal@{u v | u < v} `{Univalence} (n : trunc_index)
           (X : Type@{u}) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (@merid X).
Proof.
  (* If we post-compose [merid : X -> North = South] with an equivalence [North = South <~> P], where [P] is the pullback of the inclusions [Unit -> Susp X] hitting [North] and [South], we get the canonical comparison map [X -> P] whose connectivity follows from the Blakers-Massey theorem. *)
  snrapply cancelL_equiv_conn_map.
  - exact (Pullback (pushl (f:=const_tt X) (g:=const_tt X)) pushr).
  - symmetry.
    do 2 refine (_ oE equiv_contr_sigma _).
    reflexivity.
  - rapply blakers_massey_po@{u u u u v u u u u}.
Defined.
