Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Spaces.Nat.Core Spaces.Nat.Division Spaces.Nat.Factorial
  Tactics.EvalIn.

Local Set Universe Minimization ToSet.
Local Unset Elimination Schemes.

Local Open Scope nat_scope.

(** * Binomial coefficients *)

(** ** Definition *)

(** The binomial coefficient [nat_choose n m] is the number of ways to choose [m] elements from a set of [n] elements. We define it recursively using Pascal's identity. We use nested [Fixpoint]s in order to get a function that computes definitionally on the edge cases as well as the inductive case. *)

(** We separate out this helper result to prevent Coq from unfolding things into a larger term. This computes [n] choose [m.+1] given a function [f] that computes [n] choose [m]. *)
Fixpoint nat_choose_step n f :=
  match n with
  | 0 => 0
  | S n' => f n' + nat_choose_step n' f
  end.

Fixpoint nat_choose (n m : nat) {struct m} : nat
  := match m with
    | 0 => 1
    | S m' => nat_choose_step n (fun n => nat_choose n m')
    end.

(** We make sure we never unfold binomial coefficients with [simpl] or [cbn] since the terms do not look good. Instead, we should use lemmas we prove about it to make proofs clearer to read. *)
Arguments nat_choose n m : simpl never.

(** ** Properties *)

(** The three defining properties of [nat_choose] hold definitionally. *)

(** By definition, we have Pascal's identity. *)
Definition nat_choose_succ@{} n m
  : nat_choose n.+1 m.+1 = nat_choose n m + nat_choose n m.+1
  := idpath.

(** There is only one way to choose [0] elements from any number of elements. *)
Definition nat_choose_zero_r@{} n : nat_choose n 0 = 1
  := idpath.

(** There are no ways to choose a non-zero number of elements from [0] elements. *)
Definition nat_choose_zero_l@{} m : nat_choose 0 m.+1 = 0
  := idpath.

(** The binomial coefficient is zero if [m] is greater than [n]. *)
Definition nat_choose_lt@{} n m : n < m -> nat_choose n m = 0.
Proof.
  revert m; induction n; hnf; intros m H; destruct H.
  1, 2: reflexivity.
  1, 2: rewrite_refl nat_choose_succ; exact (ap011 nat_add (IHn _ _) (IHn _ _)).
Defined.

(** There is only one way to choose [n] elements from [n] elements. *)
Definition nat_choose_diag@{} n : nat_choose n n = 1.
Proof.
  induction n as [|n IHn]; only 1: reflexivity.
  rewrite_refl nat_choose_succ.
  rhs_V nrapply nat_add_zero_r.
  nrapply ap011.
  - exact IHn.
  - rapply nat_choose_lt.
Defined.

(** There are [n] ways to choose [1] element from [n] elements. *)
Definition nat_choose_one_r@{} n : nat_choose n 1 = n.
Proof.
  induction n as [|n IHn]; only 1: reflexivity.
  rewrite_refl nat_choose_succ.
  exact (ap nat_succ IHn).
Defined.

(** There are [n.+1] ways to choose [n] elements from [n.+1] elements. *)
Definition nat_choose_succ_l_diag@{} n : nat_choose n.+1 n = n.+1.
Proof.
  induction n as [|n IHn]; only 1: reflexivity.
  rewrite_refl nat_choose_succ.
  rhs_V nrapply (nat_add_comm _ 1).
  nrapply ap011.
  - exact IHn.
  - apply nat_choose_diag.
Defined.

(** The binomial coefficients can be written as a quotient of factorials. This is typically used as a definition of the binomial coefficients. *)
Definition nat_choose_factorial@{} n m
  : m <= n -> nat_choose n m = factorial n / (factorial m * factorial (n - m)).
Proof.
  revert n m; apply nat_double_ind_leq; intro n.
  (* The case when [m = 0]. *)
  { rewrite nat_mul_one_l.
    rewrite nat_sub_zero_r.
    symmetry; rapply nat_div_cancel. }
  (* The case when [m = n]. *)
  { rewrite nat_sub_cancel.
    rewrite nat_mul_one_r.
    rewrite nat_div_cancel.
    1: nrapply nat_choose_diag.
    exact _. }
  (* The case with [n.+1] and [m.+1] with [m < n] and an induction hypothesis. *)
  intros m H IHn.
  rewrite_refl nat_choose_succ.
  rewrite 2 IHn.
  2,3: exact _.
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
  - rewrite nat_factorial_succ.
    rewrite <- nat_mul_assoc.
    exact _.
  - rewrite <- nat_dist_r.
    rewrite nat_add_succ_l.
    rewrite nat_add_sub_r_cancel.
    2: exact _.
    rewrite <- nat_factorial_succ.
    reflexivity.
Defined.

(** Another recursive property of the binomial coefficients.  To choose [m+1] elements from a set of size [n+1], one has [n+1] choices for the first element and then can make the remaining [m] choices from the remaining [n] elements.  This overcounts by a factor of [m+1], since there are [m+1] elements that could have been called the "first" element. *)
Definition nat_choose_succ_mul@{} n m
  : nat_choose n.+1 m.+1 = (n.+1 * nat_choose n m) / m.+1.
Proof.
  destruct (leq_dichotomy m n) as [H | H].
  2: { rewrite 2 nat_choose_lt; only 2, 3: exact _.
       rewrite nat_mul_zero_r.
       symmetry; apply nat_div_zero_l. }
  rewrite 2 nat_choose_factorial.
  2,3: exact _.
  rewrite nat_div_mul_l.
  2: exact _.
  rewrite nat_div_div_l.
  by rewrite (nat_mul_comm _ m.+1), nat_mul_assoc.
Defined.

(** The binomial coefficients are symmetric about the middle of the range [0 <= n]. *)
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
