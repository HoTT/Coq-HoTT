(* -*- mode: coq; mode: visual-line -*-  *)
(** * H-Levels *)

Require Import Overture Contractible Equivalences types.Paths.
Local Open Scope equiv_scope.

Generalizable Variables A B n f.

(** A contractible space has h-level zero, of course. *)
Instance Contr_hlevel_minus_two `{HLevel minus_two A} : Contr A
  := HLevel_is_hlevel.

(** H-levels are cumulative. *)
Instance hlevel_succ `{HLevel n A} : HLevel (hlevel_S n) A.
Proof.
  generalize dependent A.
  induction n as [| n I]; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply I, H.
Qed.

(** Equivalence preserves h-levels (this is, of course, trivial with univalence).
   This is not an [Instance] because it causes infinite loops.
   *)
Definition hlevel_equiv (A B : Type) (f : A -> B)
  `{HLevel n A} `{IsEquiv A B f}
  : HLevel n B.
Proof.
  generalize dependent f; revert B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B f ?.
  - apply Contr_equiv_contr.
  - intros x y.
    refine (I (f^-1 x = f^-1 y) _ (x = y) ((ap (f^-1))^-1) _).
Qed.
