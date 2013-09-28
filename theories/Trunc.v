(* -*- mode: coq; mode: visual-line -*-  *)
(** * Truncatedness *)


Require Import Overture Contractible Equivalences types.Paths types.Unit.
Local Open Scope equiv_scope.
Local Open Scope trunc_scope.

Generalizable Variables A B m n f.

(** ** Arithmetic on truncation-levels. *)
Fixpoint trunc_index_add (m n : trunc_index) : trunc_index
  := match m with
       | minus_two => n
       | trunc_S m' => trunc_S (trunc_index_add m' n)
     end.

Notation "m -2+ n" := (trunc_index_add m n) (at level 50, left associativity) : trunc_scope.

Fixpoint trunc_index_leq (m n : trunc_index) : Type
  := match m, n with
       | minus_two, _ => Unit
       | trunc_S m', minus_two => Empty
       | trunc_S m', trunc_S n' => trunc_index_leq m' n'
     end.

Notation "m <= n" := (trunc_index_leq m n) (at level 70, no associativity) : trunc_scope.

(** ** Truncatedness proper. *)

(** A contractible space is (-2)-truncated, by definition. *)
Definition contr_trunc_minus_two `{H : IsTrunc minus_two A} : Contr A
  := H.

(** Truncation levels are cumulative. *)
Instance trunc_succ `{IsTrunc n A} : IsTrunc (trunc_S n) A | 1000.
Proof.
  generalize dependent A.
  induction n as [| n I]; simpl; intros A H x y.
  - apply contr_paths_contr.
  - apply I, H.
Qed.

Instance trunc_leq {m n} (Hmn : m <= n) `{IsTrunc m A} : IsTrunc n A | 1000.
Proof.
  generalize dependent A; generalize dependent m.
  induction n as [ | n' IH];
    intros [ | m'] Hmn A ? .
  - (* -2, -2 *) assumption.
  - (* S m', -2 *) destruct Hmn.
  - (* -2, S n' *) apply @trunc_succ, (IH minus_two); auto.
  - (* S m', S n' *) intros x y; apply (IH m');
                     auto with typeclass_instances.
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
    pose proof (fun X Y => I (f^-1 x = f^-1 y) X (x = y) ((ap (f^-1))^-1) Y).
    clear I.
    typeclasses eauto.
Qed.

Definition trunc_equiv' `(f : A <~> B) `{IsTrunc n A}
  : IsTrunc n B
  := trunc_equiv f.
