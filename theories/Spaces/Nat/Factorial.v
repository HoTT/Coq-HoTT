Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Spaces.Nat.Core Spaces.Nat.Division.

Local Set Universe Minimization ToSet.
Local Unset Elimination Schemes.

Local Open Scope nat_scope.

(** * Factorials *)

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

(** ** Divisibility *)

(** Any number less than or equal to [n] divides [factorial n]. *)
Global Instance nat_divides_facttorial_factor n m
  : 0 < n -> n <= m -> (n | factorial m).
Proof.
  intros H1 H2; destruct H1; induction H2; exact _.
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
  set (k := n + m).
  pose (p := (idpath : n + m = k)).
  clearbody k p.
  revert k n m p; snrapply nat_ind_strong; hnf; intros k IH n m p.
  destruct k.
  { apply equiv_nat_add_zero in p.
    destruct p as [p q].
    destruct p^, q^.
    exact _. }
  rewrite nat_factorial_succ.
  rewrite <- p.
  rewrite nat_dist_r.
  nrapply nat_divides_add.
  - destruct n; only 1: exact _.
    rewrite nat_factorial_succ.
    rewrite <- nat_mul_assoc.
    rapply nat_divides_mul_monotone.
    rapply IH.
    exact (ap nat_pred p).
  - destruct m; only 1: exact _.
    rewrite nat_factorial_succ.
    rewrite nat_mul_assoc.
    rewrite (nat_mul_comm (factorial n)).
    rewrite <- nat_mul_assoc.
    rapply nat_divides_mul_monotone.
    rapply IH.
    rewrite nat_add_succ_r in p.
    exact (ap nat_pred p).
Defined.

(** Here is a variant of [nat_divides_factorial_mul_factorial_add] that is more suitable for binomial coefficients. *)
Global Instance nat_divides_factorial_mul_factorial_add' n m
  : m <= n -> (factorial m * factorial (n - m) | factorial n).
Proof.
  intros H.
  set (n - m) as q;
  rewrite <- (@nat_add_sub_r_cancel m n);
  unfold q; clear q; exact _. 
Defined.
