Require Import Basics Types Limits.Pullback Colimits.Pushout.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Homotopy.Suspension Homotopy.BlakersMassey.

(** * The Freudenthal Suspension Theorem *)

(** The Freudenthal suspension theorem is a fairly trivial corollary of the Blakers-Massey theorem.  It says that [merid : X -> North = South] is highly connected. *)
Global Instance freudenthal `{Univalence} (n : trunc_index)
           (X : Type@{u}) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (@merid X).
Proof.
  (* If we post-compose [merid : X -> North = South] with an equivalence [North = South <~> P], where [P] is the pullback of the inclusions [Unit -> Susp X] hitting [North] and [South], we get the canonical comparison map [X -> P] whose connectivity follows from the Blakers-Massey theorem. *)
  rapply (cancelL_equiv_conn_map _ _ (equiv_pullback_unit_unit_paths _ _)^-1%equiv).
  rapply blakers_massey_po.
Defined.
