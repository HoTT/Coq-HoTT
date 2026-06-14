From HoTT Require Import Basics Types Truncations.Core.
From HoTT.WildCat Require Import Core.
Require Import Spaces.Int Spaces.Nat.Core Spaces.Nat.Division.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.Z.
Require Import Algebra.Rings.Ring Algebra.Rings.CRing Algebra.Rings.Z
  Algebra.Rings.Bezout.

Local Open Scope mc_scope.

(** * The integers form a Bézout domain *)

(** The absolute value of an integer, as a natural number. *)
Definition int_abs (x : Int) : nat :=
  match x with
  | negS n => n.+1
  | posS n => n.+1
  | _ => 0%nat
  end.

Definition int_abs_of_nat (n : nat) : int_abs (int_of_nat n) = n.
Proof.
  by destruct n.
Defined.

Definition int_abs_neg (x : Int) : int_abs (int_neg x) = int_abs x.
Proof.
  by destruct x.
Defined.

(** Every integer is its absolute value up to sign. *)
Definition int_abs_decomp (x : Int)
  : (x = int_of_nat (int_abs x)) + (x = int_neg (int_of_nat (int_abs x))).
Proof.
  destruct x.
  - exact (inr idpath).
  - exact (inl idpath).
  - exact (inl idpath).
Defined.

(** Absolute value of a product of two naturals coerced into [Int]. *)
Definition int_abs_of_nat_mul (a b : nat)
  : int_abs (int_mul (int_of_nat a) (int_of_nat b)) = (a * b)%nat
  := ap int_abs (int_nat_mul a b) @ int_abs_of_nat (a * b).

(** Absolute value is multiplicative. *)
Definition int_abs_mul (x y : Int)
  : int_abs (int_mul x y) = (int_abs x * int_abs y)%nat.
Proof.
  destruct (int_abs_decomp x) as [px | px], (int_abs_decomp y) as [py | py];
    lhs napply (ap int_abs (ap011 int_mul px py)).
  - napply int_abs_of_nat_mul.
  - lhs napply (ap int_abs (int_mul_neg_r _ _)).
    lhs napply int_abs_neg.
    napply int_abs_of_nat_mul.
  - lhs napply (ap int_abs (int_mul_neg_l _ _)).
    lhs napply int_abs_neg.
    napply int_abs_of_nat_mul.
  - lhs napply (ap int_abs (int_mul_neg_l _ _)).
    lhs napply int_abs_neg.
    lhs napply (ap int_abs (int_mul_neg_r _ _)).
    lhs napply int_abs_neg.
    napply int_abs_of_nat_mul.
Defined.

(** An integer with trivial absolute value is zero. *)
Definition int_abs_is_zero {x : cring_Z} (p : int_abs x = 0%nat) : x = 0.
Proof.
  destruct x.
  - exact (Empty_rec (neq_nat_zero_succ _ p^)).
  - reflexivity.
  - exact (Empty_rec (neq_nat_zero_succ _ p^)).
Defined.

(** A product of naturals vanishes only if a factor does. *)
Definition nat_mul_is_zero {a b : nat} (p : (a * b)%nat = 0%nat)
  : (a = 0%nat) + (b = 0%nat).
Proof.
  destruct a as [|a]; [ exact (inl idpath) | ].
  destruct b as [|b]; [ exact (inr idpath) | ].
  napply Empty_rec.
  exact (neq_nat_zero_succ _ (p^ @ nat_mul_succ_l a b.+1 @ nat_add_succ_l b _)).
Defined.

(** [cring_Z] has no zero divisors. *)
Definition int_mul_is_zero {x y : cring_Z} (p : x * y = 0)
  : (x = 0) + (y = 0).
Proof.
  assert (q : (int_abs x * int_abs y)%nat = 0%nat)
    by exact ((int_abs_mul x y)^ @ ap int_abs p).
  destruct (nat_mul_is_zero q) as [hx | hy].
  - exact (inl (int_abs_is_zero hx)).
  - exact (inr (int_abs_is_zero hy)).
Defined.

(** The integers form an integral domain. *)
Instance isintegraldomain_cring_Z : IsIntegralDomain cring_Z.
Proof.
  intro x.
  destruct (dec (x = 0)) as [p | np].
  - exact (inl p).
  - right; intros y z h.
    assert (hxyz : x * (y - z) = 0).
    { lhs napply rng_dist_l.
      lhs napply (ap (fun w => x * y + w) (rng_mult_negate_r x z)).
      lhs napply (ap (fun w => w - x * z) h).
      exact (right_inverse (x * z)). }
    destruct (int_mul_is_zero hxyz) as [h0 | hyz].
    + exact (Empty_rec (np h0)).
    + napply grp_moveL_1M; exact hyz.
Defined.
