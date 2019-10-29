(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.

Local Open Scope nat_scope.
Local Open Scope path_scope.

(** * Cantor space 2^N *)

Definition Cantor : Type := nat -> Bool.

Definition cantor_fold : Cantor + Cantor -> Cantor.
Proof.
  intros [c|c]; intros n.
  - destruct n as [|n].
    + exact true.
    + exact (c n).
  - destruct n as [|n].
    + exact false.
    + exact (c n).
Defined.

Definition cantor_unfold : Cantor -> Cantor + Cantor.
Proof.
  intros c.
  case (c 0).
  - exact (inl (fun n => c n.+1)).
  - exact (inr (fun n => c n.+1)).
Defined.

Global Instance isequiv_cantor_fold `{Funext} : IsEquiv cantor_fold.
Proof.
  refine (isequiv_adjointify _ cantor_unfold _ _).
  - intros c; apply path_arrow; intros n.
    induction n as [|n IH].
    + unfold cantor_unfold.
      case (c 0); reflexivity.
    + unfold cantor_unfold.
      case (c 0); reflexivity.
  - intros [c|c]; apply path_sum; reflexivity.
Defined.

Definition equiv_cantor_fold `{Funext} : Cantor + Cantor <~> Cantor
  := Build_Equiv _ _ cantor_fold _.

Definition equiv_cantor_unfold `{Funext} : Cantor <~> Cantor + Cantor
  := Build_Equiv _ _ cantor_unfold (isequiv_inverse equiv_cantor_fold).
