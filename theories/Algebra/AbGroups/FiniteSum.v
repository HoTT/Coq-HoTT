Require Import Basics.Overture Basics.Tactics.
Require Import Spaces.Nat.Core Spaces.Int.
Require Export Classes.interfaces.canonical_names (Commutative).
Require Export Classes.interfaces.abstract_algebra (IsAbGroup(..), abgroup_group, abgroup_commutative).
Require Import AbelianGroup.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * Finite Sums *)

(** Indexed finite sum of abelian group elements. *)
Definition ab_sum {A : AbGroup} (n : nat) (f : forall k, (k < n)%nat -> A) : A.
Proof.
  induction n as [|n IHn].
  - exact 0.
  - refine (f n _ + IHn _).
    intros k Hk.
    exact (f k _).
Defined.

(** If the function is constant in the range of a finite sum then the sum is equal to the constant times [n]. This is a group power in the underlying group. *)
Definition ab_sum_const {A : AbGroup} (n : nat) (a : A)
  (f : forall k, (k < n)%nat -> A) (p : forall k Hk, f k Hk = a)
  : ab_sum n f = ab_mul n a.
Proof.
  induction n as [|n IHn] in f, p |- *.
  - reflexivity.
  - rhs_V nrapply (ap@{Set _} _ (int_nat_succ n)).
    rhs nrapply grp_pow_succ.
    simpl. f_ap.
    apply IHn.
    intros. apply p.
Defined.

(** If the function is zero in the range of a finite sum then the sum is zero. *)
Definition ab_sum_zero {A : AbGroup} (n : nat)
  (f : forall k, (k < n)%nat -> A) (p : forall k Hk, f k Hk = 0)
  : ab_sum n f = 0.
Proof.
  lhs nrapply (ab_sum_const _ 0 f p).
  apply grp_pow_unit.
Defined.

(** Finite sums distribute over addition. *)
Definition ab_sum_plus {A : AbGroup} (n : nat) (f g : forall k, (k < n)%nat -> A)
  : ab_sum n (fun k Hk => f k Hk + g k Hk)
    = ab_sum n (fun k Hk => f k Hk) + ab_sum n (fun k Hk => g k Hk).
Proof.
  induction n as [|n IHn].
  1: by rewrite grp_unit_l.
  simpl.
  rewrite <- !grp_assoc; f_ap.
  rewrite IHn, abgroup_commutative, <- grp_assoc; f_ap.
  by rewrite abgroup_commutative.
Defined.

(** Double finite sums commute. *)
Definition ab_sum_sum {A : AbGroup} (m n : nat)
  (f : forall i j, (i < m)%nat -> (j < n)%nat -> A)
  : ab_sum m (fun i Hi => ab_sum n (fun j Hj => f i j Hi Hj))
   = ab_sum n (fun j Hj => ab_sum m (fun i Hi => f i j Hi Hj)).
Proof.
  induction n as [|n IHn] in m, f |- *.
  1: by nrapply ab_sum_zero.
  lhs nrapply ab_sum_plus; cbn; f_ap.
Defined.

(** Finite sums are equal if the functions are equal in the range. *)
Definition path_ab_sum {A : AbGroup} {n : nat} {f g : forall k, (k < n)%nat -> A}
  (p : forall k Hk, f k Hk = g k Hk)
  : ab_sum n f = ab_sum n g.
Proof.
  induction n as [|n IHn].
  1: reflexivity.
  cbn; f_ap.
  by apply IHn.
Defined.
