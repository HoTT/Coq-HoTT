(* -*- mode: coq; mode: visual-line -*-  *)
(** * H-Levels *)

Require Import Overture Contractible Equivalences types.Paths.
Local Open Scope equiv_scope.

Generalizable Variables A B n f.

(** A contractible space is (-2)-truncated, of course. *)
Instance Contr_trunc_minus_two `{Trunc minus_two A} : Contr A
  := Trunc_is_trunc.

(** Truncation levels are cumulative. *)
Instance trunc_succ `{Trunc n A} : Trunc (trunc_S n) A.
Proof.
  generalize dependent A.
  induction n as [| n I]; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply I, H.
Qed.

(** Equivalence preserves truncation (this is, of course, trivial with univalence).
   This is not an [Instance] because it causes infinite loops.
   *)
Definition trunc_equiv (A B : Type) (f : A -> B)
  `{Trunc n A} `{IsEquiv A B f}
  : Trunc n B.
Proof.
  generalize dependent f; revert B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B f ?.
  - apply Contr_equiv_contr.
  - intros x y.
    refine (I (f^-1 x = f^-1 y) _ (x = y) ((ap (f^-1))^-1) _).
Qed.
