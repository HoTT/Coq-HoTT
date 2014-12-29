(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Cantor space 2^N *)

Definition cantor : Type := nat -> Bool.

Definition fold_cantor : cantor + cantor -> cantor.
Proof.
  intros [c|c]; intros n.
  - destruct n as [|n].
    + exact true.
    + exact (c n).
  - destruct n as [|n].
    + exact false.
    + exact (c n).
Defined.

Definition unfold_cantor : cantor -> cantor + cantor.
Proof.
  intros c.
  case (c 0).
  - exact (inl (fun n => c n.+1)).
  - exact (inr (fun n => c n.+1)).
Defined.

Global Instance isequiv_fold_cantor `{Funext} : IsEquiv fold_cantor.
Proof.
  refine (isequiv_adjointify fold_cantor unfold_cantor _ _).
  - intros c; apply path_arrow; intros n.
    induction n as [|n IH].
    + unfold unfold_cantor.
      case (c 0); reflexivity.
    + unfold unfold_cantor.
      case (c 0); reflexivity.
  - intros [c|c]; apply path_sum; reflexivity.
Defined.

Definition equiv_fold_cantor `{Funext} : cantor + cantor <~> cantor
  := BuildEquiv _ _ fold_cantor _.
