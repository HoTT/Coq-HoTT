From HoTT Require Import Basics Types Truncations.Core.
Require Import Spaces.Int Spaces.Nat.Core Spaces.Nat.Division.
Require Import Algebra.Rings.Ring Algebra.Rings.CRing Algebra.Rings.Z
  Algebra.Rings.Bezout.

Local Open Scope mc_scope.

(** * The integers form a Bézout domain *)

(** An integer with trivial absolute value is zero. *)
Definition int_abs_is_zero {x : cring_Z} (p : int_abs x = 0%nat) : x = 0.
Proof.
  destruct x.
  - exact (Empty_rec (neq_nat_zero_succ _ p^)).
  - reflexivity.
  - exact (Empty_rec (neq_nat_zero_succ _ p^)).
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

(** A divisibility of naturals lifts to the integers. *)
Definition rng_divides_int_nat {d n : nat} (h : (d | n)%nat)
  : rng_divides (R:=cring_Z) (int_of_nat d) (int_of_nat n).
Proof.
  destruct h as [k p].
  apply tr; exists (int_of_nat k).
  exact ((ap int_of_nat p)^ @ (int_nat_mul k d)^).
Defined.

(** Divisibility by [g] only depends on the dividend up to sign. *)
Definition rng_divides_int_abs_r {g x : cring_Z}
  (h : rng_divides g (int_of_nat (int_abs x))) : rng_divides g x.
Proof.
  destruct (int_abs_decomp x) as [px | px].
  - exact (transport (rng_divides g) px^ h).
  - exact (transport (rng_divides g) px^ (rng_divides_negate_r h)).
Defined.

(** Bézout's identity for the integers, on nonnegative representatives. *)
Definition int_bezout_nat (a b : nat)
  : merely { u : Int & { v : Int
      & (u * int_of_nat a + v * int_of_nat b)%int = int_of_nat (nat_gcd a b) } }.
Proof.
  destruct a as [|a].
  - apply tr; exists 0%int, 1%int.
    exact (ap011 int_add (int_mul_0_l _) (int_mul_1_l _) @ int_add_0_l _).
  - pose proof (nat_bezout_pos_l a.+1 b _) as hbz.
    destruct hbz as [c [e r]].
    apply tr; exists (int_of_nat c), (- int_of_nat e)%int.
    pose (Rint := int_nat_mul c a.+1 @ ap int_of_nat r @ (int_nat_add _ _)^
                  @ ap (fun w => (int_of_nat (nat_gcd a.+1 b) + w)%int)
                       (int_nat_mul e b)^).
    lhs napply (ap (fun w => (w + (- int_of_nat e) * int_of_nat b)%int) Rint).
    lhs_V napply int_add_assoc.
    exact (ap (fun w => (int_of_nat (nat_gcd a.+1 b) + w)%int)
              ((int_dist_r (int_of_nat e) (- int_of_nat e) (int_of_nat b))^
               @ ap (fun s => (s * int_of_nat b)%int) (int_add_neg_r (int_of_nat e))
               @ int_mul_0_l (int_of_nat b))
           @ int_add_0_r (int_of_nat (nat_gcd a.+1 b))).
Defined.

(** Rewriting a multiple of [|x|] as a multiple of [x], absorbing the sign. *)
Definition int_abs_to_var (u x : cring_Z)
  : { U : cring_Z & u * (int_of_nat (int_abs x) : cring_Z) = U * x }.
Proof.
  destruct (int_abs_decomp x) as [px | px].
  - exists u; exact (ap (fun w => u * w) px^).
  - exists (- u).
    exact ((rng_mult_negate_l u (- (int_of_nat (int_abs x) : cring_Z))
            @ ap (fun w => - w) (rng_mult_negate_r u (int_of_nat (int_abs x) : cring_Z))
            @ negate_involutive (u * (int_of_nat (int_abs x) : cring_Z)))^
           @ ap (fun w => (- u) * w) px^).
Defined.

(** The integers form a Bézout ring: any two have a gcd that is a Bézout
    combination of them. *)
Instance isbezoutring_cring_Z : IsBezoutRing cring_Z.
Proof.
  intros x y.
  pose proof (int_bezout_nat (int_abs x) (int_abs y)) as hbz.
  strip_truncations; destruct hbz as [u0 [v0 hcombo]].
  destruct (int_abs_to_var u0 x) as [U pU].
  destruct (int_abs_to_var v0 y) as [V pV].
  pose (combo := (ap011 (+) pU pV)^ @ hcombo).
  apply tr; exists U, V.
  refine (_, _, _).
  - exact (transport (fun w => rng_divides w x) combo^
             (rng_divides_int_abs_r
                (rng_divides_int_nat (nat_divides_l_gcd_l (int_abs x) (int_abs y))))).
  - exact (transport (fun w => rng_divides w y) combo^
             (rng_divides_int_abs_r
                (rng_divides_int_nat (divides_l_nat_gcd_r (int_abs x) (int_abs y))))).
  - intros z hzx hzy.
    exact (rng_divides_plus (rng_divides_mul_l U hzx) (rng_divides_mul_l V hzy)).
Defined.

(** Hence the integers form a Bézout domain. *)
Instance isbezoutdomain_cring_Z : IsBezoutDomain cring_Z := {}.
