(* -*- mode: coq; mode: visual-line -*-  *)
(** * H-Levels *)

Require Import Overture Contractible Equivalences types.Paths.
Local Open Scope equiv_scope.

Generalizable Variables A B n f.

(** A contractible space is (-2)-truncated, of course. *)
Instance contr_trunc_minus_two `{IsTrunc minus_two A} : Contr A
  := Trunc_is_trunc.

(** Truncation levels are cumulative. *)
Instance trunc_succ `{IsTrunc n A} : IsTrunc (trunc_S n) A.
Proof.
  generalize dependent A.
  induction n as [| n I]; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply I, H.
Qed.

(** Equivalence preserves truncation (this is, of course, trivial with univalence).
   This is not an [Instance] because it causes infinite loops.
   *)
Definition trunc_equiv `(f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent f; revert B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B f ?.
  - refine (contr_equiv f).
  - intros x y.
    refine (I (f^-1 x = f^-1 y) _ (x = y) ((ap (f^-1))^-1) _).
Qed.

Definition trunc_equiv' `(f : A <~> B) `{IsTrunc n A}
  : IsTrunc n B
  := trunc_equiv f.

(** Arithmetic on truncation-levels. *)
Fixpoint trunc_add (m n : trunc_index) : trunc_index
  := match m with
       | minus_two => n
       | trunc_S m' => trunc_S (trunc_add m' n)
     end.

Notation "m -2+ n" := (trunc_add m n) (at level 50, left associativity).
