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

(** A divisibility of naturals lifts to the integers. *)
Definition rng_divides_int_nat {d n : nat} (h : (d | n)%nat)
  : rng_divides (R:=cring_Z) (int_of_nat d) (int_of_nat n).
Proof.
  destruct h as [k p].
  apply tr; exists (int_of_nat k).
  exact ((ap int_of_nat p)^ @ (int_nat_mul k d)^).
Defined.

(** Divisibility is preserved under negating the dividend. *)
Definition rng_divides_neg_r {g x : cring_Z} (h : rng_divides g x)
  : rng_divides g (- x).
Proof.
  strip_truncations; destruct h as [c p].
  apply tr; exists (- c).
  exact (ap (fun w => - w) p @ (rng_mult_negate_l c g)^).
Defined.

(** Divisibility is preserved under negating the divisor. *)
Definition rng_divides_neg_l {g x : cring_Z} (h : rng_divides g x)
  : rng_divides (- g) x.
Proof.
  strip_truncations; destruct h as [c p].
  apply tr; exists (- c).
  exact (p @ (rng_mult_negate_r (- c) g
              @ ap (fun w => - w) (rng_mult_negate_l c g)
              @ negate_involutive (c * g))^).
Defined.

(** Divisibility by [g] only depends on the dividend up to sign. *)
Definition rng_divides_int_abs_r {g x : cring_Z}
  (h : rng_divides g (int_of_nat (int_abs x))) : rng_divides g x.
Proof.
  destruct (int_abs_decomp x) as [px | px].
  - exact (transport (rng_divides g) px^ h).
  - exact (transport (rng_divides g) px^ (rng_divides_neg_r h)).
Defined.

(** Divisibility only depends on the divisor up to sign. *)
Definition rng_divides_int_abs_l {g x : cring_Z}
  (h : rng_divides (int_of_nat (int_abs g) : cring_Z) x) : rng_divides g x.
Proof.
  destruct (int_abs_decomp g) as [pg | pg].
  - exact (transport (fun w => rng_divides w x) pg^ h).
  - exact (transport (fun w => rng_divides w x) pg^ (rng_divides_neg_l h)).
Defined.

(** An integer divisibility restricts to a divisibility of absolute values. *)
Definition nat_divides_of_rng_divides {z w c : cring_Z} (p : w = c * z)
  : (int_abs z | int_abs w)%nat.
Proof.
  exists (int_abs c).
  exact ((int_abs_mul c z)^ @ (ap int_abs p)^).
Defined.

(** A natural number as an element of the ring [cring_Z], pinning the typing so
    that ring operations resolve without flipping back to [Int]. *)
Definition znat (n : nat) : cring_Z := int_of_nat n.

Definition znat_mul (a b : nat) : znat (a * b) = znat a * znat b
  := (int_nat_mul a b)^.

Definition znat_add (a b : nat) : znat (a + b) = znat a + znat b
  := (int_nat_add a b)^.

(** Bézout's identity for the integers, on nonnegative representatives. *)
Definition int_bezout_nat (a b : nat)
  : merely { u : cring_Z & { v : cring_Z
      & u * znat a + v * znat b = znat (nat_gcd a b) } }.
Proof.
  destruct a as [|a].
  - apply tr; exists 0, 1.
    exact (ap011 (+) (rng_mult_zero_l (znat 0)) (rng_mult_one_l (znat b))
           @ left_identity (znat b)).
  - pose proof (nat_bezout_pos_l a.+1 b _) as hbz.
    destruct hbz as [c [e r]].
    apply tr; exists (znat c), (- znat e).
    pose (Rint := (znat_mul c a.+1)^ @ ap znat r @ znat_add _ _
                  @ ap (fun w => znat (nat_gcd a.+1 b) + w) (znat_mul e b)).
    lhs napply (ap (fun w => w + (- znat e) * znat b) Rint).
    lhs_V napply grp_assoc.
    exact (ap (fun w => znat (nat_gcd a.+1 b) + w)
              ((rng_dist_r (znat e) (- znat e) (znat b))^
               @ ap (fun s => s * znat b) (right_inverse (znat e))
               @ rng_mult_zero_l (znat b))
           @ right_identity (znat (nat_gcd a.+1 b))).
Defined.

(** Rewriting a multiple of [|x|] as a multiple of [x], absorbing the sign. *)
Definition znat_abs_to_var (u x : cring_Z)
  : { U : cring_Z & u * znat (int_abs x) = U * x }.
Proof.
  destruct (int_abs_decomp x) as [px | px].
  - exists u; exact (ap (fun w => u * w) px^).
  - exists (- u).
    exact ((rng_mult_negate_l u (- znat (int_abs x))
            @ ap (fun w => - w) (rng_mult_negate_r u (znat (int_abs x)))
            @ negate_involutive (u * znat (int_abs x)))^
           @ ap (fun w => (- u) * w) px^).
Defined.

(** The integers form a Bézout ring: any two have a gcd that is a Bézout
    combination of them. *)
Instance isbezoutring_cring_Z : IsBezoutRing cring_Z.
Proof.
  intros x y.
  pose proof (int_bezout_nat (int_abs x) (int_abs y)) as hbz.
  strip_truncations; destruct hbz as [u0 [v0 hcombo]].
  destruct (znat_abs_to_var u0 x) as [U pU].
  destruct (znat_abs_to_var v0 y) as [V pV].
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
