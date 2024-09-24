Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Spaces.Nat.Core Spaces.Nat.Division Tactics.EvalIn.

Local Set Universe Minimization ToSet.

Local Open Scope nat_scope.

(** * Factorials *)

(** ** Definition *)

Fixpoint factorial n := 
  match n with
  | 0 => 1
  | S n => S n * factorial n
  end.

(** ** Properties *)

(** The factorial of [0] is [1]. *)
Definition nat_factorial_zero : factorial 0 = 1 := idpath.

(** The factorial of [n + 1] is [n + 1] times the factorial of [n]. *)
Definition nat_factorial_succ n : factorial n.+1 = n.+1 * factorial n
  := idpath.

(** A variant of [nat_factorial_succ]. *)
Definition nat_factorial_pred n
  : 0 < n -> factorial n = n * factorial (nat_pred n).
Proof.
  intros []; reflexivity.
Defined.

(** Every factorial is positive. *)
Global Instance lt_zero_factorial n : 0 < factorial n.
Proof.
  induction n; exact _.
Defined.

(** Except for [factorial 0 = factorial 1], the [factorial] function is strictly monotone.  We separate out the successor case since it is used twice in the proof of the general result. *)
Definition nat_factorial_strictly_monotone_succ n
  : 0 < n -> factorial n < factorial n.+1.
Proof.
  intro H.
  rewrite <- (nat_mul_one_l (factorial n)).
  rapply (nat_mul_r_strictly_monotone _).
Defined.

Global Instance nat_factorial_strictly_monotone n m
  : 0 < n -> n < m -> factorial n < factorial m.
Proof.
  intros H1 H2; induction H2.
  - rapply nat_factorial_strictly_monotone_succ.
  - apply (lt_trans IHleq).
    rapply nat_factorial_strictly_monotone_succ.
Defined.

(** ** Divisibility *)

(** Any number less than or equal to [n] divides [factorial n]. *)
Global Instance nat_divides_factorial_factor n m
  : 0 < n -> n <= m -> (n | factorial m).
Proof.
  intros [] H2.
  1: exact _.
  induction H2; exact _.
Defined.

(** [factorial] is a monotone function from [nat] to [nat] with respect to [<=] and divides. *)
Global Instance nat_divides_factorial_lt n m
  : n <= m -> (factorial n | factorial m).
Proof.
  intros H; induction H; exact _.
Defined.

(** A product of factorials divides the factorial of the sum. *)
Global Instance nat_divides_factorial_mul_factorial_add n m
  : (factorial n * factorial m | factorial (n + m)).
Proof.
  remember (n + m) as k eqn:p.
  revert k n m p; snrapply nat_ind_strong; hnf; intros k IH n m p.
  destruct k.
  { apply equiv_nat_add_zero in p.
    destruct p as [p q].
    destruct p^, q^.
    exact _. }
  rewrite_refl nat_factorial_succ.
  rewrite <- p.
  rewrite nat_dist_r.
  assert (helper : forall n' m' (p' : n' + m' = k.+1), (factorial n' * factorial m' | n' * factorial k)).
  - intros n' m' p'.
    destruct n'; only 1: exact _.
    rewrite nat_factorial_succ.
    rewrite <- nat_mul_assoc.
    rapply nat_divides_mul_monotone.
    rapply IH.
    exact (ap nat_pred p').
  - nrapply nat_divides_add.
    + apply helper, p.
    + rewrite nat_mul_comm.
      apply helper.
      lhs nrapply nat_add_comm; exact p.
Defined.

(** Here is a variant of [nat_divides_factorial_mul_factorial_add] that is more suitable for binomial coefficients. *)
Global Instance nat_divides_factorial_mul_factorial_add' n m
  : m <= n -> (factorial m * factorial (n - m) | factorial n).
Proof.
  intros H.
  rewrite <- (ap factorial (nat_add_sub_r_cancel H)).
  apply nat_divides_factorial_mul_factorial_add.
Defined.
