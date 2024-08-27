Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Spaces.Nat.Core Spaces.Nat.Division Spaces.Nat.Factorial.

Local Set Universe Minimization ToSet.
Local Unset Elimination Schemes.

Local Open Scope nat_scope.

(** * Binomial coefficients *)

(** ** Definition *)

(** The binomial coefficient [nat_choose n m] is the number of ways to choose [m] elements from a set of [n] elements. We define them recursively using Pascal's identity. *)
Fixpoint nat_choose n m :=
  match m with
  | 0 => 1
  | S m =>
    match n with
    | 0 => 0
    | S n => nat_choose n m + nat_choose n m.+1
    end
  end.

(** ** Properties *)

(** By definition, we have Pascal's identity. *)
Definition nat_choose_succ@{} n m
  : nat_choose n.+1 m.+1 = nat_choose n m + nat_choose n m.+1
  := idpath.

(** The binomial coefficient is zero if [m] is greater than [n]. *)
Definition nat_choose_lt@{} n m : n < m -> nat_choose n m = 0.
Proof.
  revert n m; snrapply nat_ind_strong; hnf; intros n IHn m H.
  destruct H, n; only 1,3: reflexivity;
  exact (ap011 nat_add (IHn _ _ _ _) (IHn _ _ _ _)).
Defined.

(** There is only one way to choose [n] elements from [n] elements. *)
Definition nat_choose_diag@{} n : nat_choose n n = 1.
Proof.
  induction n as [|n IHn]; only 1: reflexivity.
  simpl; lhs nrapply ap.
  1: rapply nat_choose_lt.
  lhs nrapply nat_add_zero_r.
  exact IHn.
Defined.

(** There are no ways to choose more than [0] elements from [0] elements. *)
Definition nat_choose_zero_l@{} n : 0 < n -> nat_choose 0 n = 0.
Proof.
  intros H; destruct H; reflexivity.
Defined.

(** There is only one way to choose [0] elements from any number of elements. *)
Definition nat_choose_zero_r@{} n : nat_choose n 0 = 1.
Proof.
  by destruct n.
Defined.

(** There are [n] ways to choose [1] element from [n] elements. *)
Definition nat_choose_one_r@{} n : nat_choose n 1 = n.
Proof.
  induction n as [|n IHn].
  1: reflexivity.
  simpl.
  lhs nrapply (ap (fun x => x + _)).
  1: apply nat_choose_zero_r.
  exact (ap nat_succ IHn).
Defined.

(** There are [n.+1] ways to choose [n] elements from [n.+1] elements. *)
Definition nat_choose_succ_l_diag@{} n : nat_choose n.+1 n = n.+1.
Proof.
  induction n as [|n IHn].
  1: reflexivity.
  lhs nrapply nat_choose_succ.
  rewrite IHn, nat_choose_diag.
  apply nat_add_comm.
Defined.

(** The binomial coefficients can be written as a quotient of factorials. This is typically used as a definition of the binomial coefficients. *)
Definition nat_choose_factorial@{} n m
  : m <= n -> nat_choose n m = factorial n / (factorial m * factorial (n - m)).
Proof.
  revert n m; snrapply nat_ind_strong; hnf; intros n IHn m H.
  destruct H as [|n H].
  { rewrite nat_sub_cancel.
    rewrite nat_mul_one_r.
    rewrite nat_div_cancel.
    1: nrapply nat_choose_diag.
    exact _. }
  destruct m.
  { rewrite nat_choose_zero_r.
    rewrite nat_sub_zero_r.
    rewrite nat_mul_one_l.
    symmetry.
    apply nat_div_cancel.
    exact _. }
  rewrite nat_choose_succ.
  rewrite 2 IHn.
  2-5: exact _.
  rewrite <- (nat_div_cancel_mul_l _ _ m.+1). 
  2: exact _.
  rewrite nat_mul_assoc.
  rewrite <- nat_factorial_succ.
  rewrite <- (nat_div_cancel_mul_l (factorial n) _ (n - m)).
  2: rapply equiv_lt_lt_sub.
  rewrite nat_mul_assoc.
  rewrite (nat_mul_comm (n - m) (factorial m.+1)).
  rewrite <- nat_mul_assoc.
  rewrite nat_sub_succ_r.
  rewrite <- nat_factorial_pred.
  2: rapply equiv_lt_lt_sub.
  lhs_V nrapply nat_div_dist.
  - change (n - m) with (n.+1 - m.+1).
    rewrite nat_dist_sub_r.
    rapply nat_divides_sub.
    change (n.+1 - m.+1) with (n - m).
    rewrite nat_factorial_succ.
    rewrite <- nat_mul_assoc.
    exact _.
  - rewrite nat_factorial_succ.
    rewrite <- nat_mul_assoc.
    exact _.
  - rapply lt_lt_leq_trans.
  - rewrite <- nat_dist_r.
    rewrite nat_add_succ_l.
    rewrite nat_add_sub_r_cancel.
    2: exact _.
    rewrite <- nat_factorial_succ.
    reflexivity.
Defined.

Definition nat_choose_succ_mul@{} n m
  : m <= n -> nat_choose n.+1 m.+1 = (n.+1 * nat_choose n m) / m.+1. 
Proof.
  intros H.
  rewrite 2 nat_choose_factorial.
  2,3: exact _.
  rewrite nat_div_mul_l.
  2: exact _.
  rewrite nat_div_div_l; rewrite (nat_mul_comm _ m.+1), nat_mul_assoc.
  1: reflexivity.
  change (factorial m.+1 * factorial (n.+1 - m.+1) | factorial n.+1).
  exact _.
Defined.

Definition nat_choose_sub@{} n m
  : m <= n -> nat_choose n m = nat_choose n (n - m).
Proof.
  intros H.
  rewrite 2 nat_choose_factorial.
  2,3: exact _.
  rewrite nat_sub_sub_cancel_r.
  2: exact _.
  by rewrite nat_mul_comm.
Defined.
