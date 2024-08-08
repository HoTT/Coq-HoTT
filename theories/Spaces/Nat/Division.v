Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Basics.Trunc Basics.Equivalences Basics.Nat Basics.Classes
  Types.Sum Types.Sigma Spaces.Nat.Core.

Local Open Scope nat_scope.

(** ** Divisibility *)

(** We define divisibility as a relation between natural numbers. *)
Class NatDivides (n m : nat) : Type0 := nat_divides : {k : nat & k * n = m}.

Notation "( n | m )" := (NatDivides n m) : nat_scope.

(** Any number divides [0]. *)
Global Instance nat_divides_zero_r n : (n | 0)
  := (0; idpath).

(** [1] divides any number. *)
Global Instance nat_divides_one_l n : (1 | n)
  := (n; nat_mul_one_r _).

(** Any number divides itself. Divisibility is a reflexive relation. *)
Global Instance nat_divides_refl n : (n | n)
  := (1; nat_mul_one_l _).

Global Instance reflexive_nat_divides : Reflexive NatDivides := nat_divides_refl.

(** Divisibility is transitive. *)
Definition nat_divides_trans {n m l} : (n | m) -> (m | l) -> (n | l).
Proof.
  intros [x p] [y q].
  exists (y * x).
  lhs_V nrapply nat_mul_assoc.
  lhs nrapply (ap _ p).
  exact q.
Defined.
Hint Immediate nat_divides_trans : typeclass_instances.

Global Instance transitive_nat_divides : Transitive NatDivides := @nat_divides_trans.

(** A left factor divides a product. *)
Global Instance nat_divides_mul_l' n m : (n | n * m)
  := (m; nat_mul_comm _ _).

(** A right factor divides a product. *)
Global Instance nat_divides_mul_r' n m : (m | n * m)
  := (n; idpath).

(** Divisibility of the product is implied by divisibility of the left factor. *)
Global Instance nat_divides_mul_l {n m} l : (n | m) -> (n | m * l)
  := fun H => nat_divides_trans _ _.

(** Divisibility of the product is implied by divisibility of the right factor. *)
Global Instance nat_divides_mul_r {n m} l : (n | m) -> (n | l * m)
  := fun H => nat_divides_trans _ _.

(** Divisibility of the sum is implied by divisibility of the summands. *)
Global Instance nat_divides_add n m l : (n | m) -> (n | l) -> (n | m + l).
Proof.
  intros [x p] [y q].
  exists (x + y).
  destruct p, q.
  nrapply nat_dist_r.
Defined.

(** If [n] divides a sum and the left summand, then [n] divides the right summand. *)
Definition nat_divides_add_r n m l : (n | m) -> (n | m + l) -> (n | l).
Proof.
  intros [x p] [y q].
  exists (y - x).
  lhs nrapply nat_dist_sub_r.
  apply nat_moveR_nV.
  lhs nrapply q.
  lhs nrapply nat_add_comm.
  exact (ap _ p^).
Defined.

(** If [n] divides a sum and the right summand, then [n] divides the left summand. *)
Definition nat_divides_add_l n m l : (n | l) -> (n | m + l) -> (n | m).
Proof.
  rewrite nat_add_comm; apply nat_divides_add_r.
Defined.

(** Divisibility of the difference is implied by divisibility of the minuend and subtrahend. *)
Global Instance nat_divides_sub n m l : (n | m) -> (n | l) -> (n | m - l).
Proof.
  intros [x p] [y q].
  exists (x - y).
  destruct p, q.
  nrapply nat_dist_sub_r.
Defined.

(** Divisibility implies that the divisor is less than or equal to the dividend. *)
Definition leq_divides n m : 0 < m -> (n | m) -> n <= m.
Proof.
  intros H1 [x p].
  destruct p, x.
  1: contradiction (not_lt_zero_r _ H1).
  rapply (leq_mul_l _ _ 0).
Defined.

(** Divisibility is antisymmetric *)
Definition nat_divides_antisym n m : (n | m) -> (m | n) -> n = m.
Proof.
  intros H1 H2.
  destruct m; only 1: exact (H2.2^ @ nat_mul_zero_r _).
  destruct n; only 1: exact ((nat_mul_zero_r _)^ @ H1.2).
  snrapply leq_antisym; nrapply leq_divides; exact _.
Defined.

Global Instance antisymmetric_divides : AntiSymmetric NatDivides
  := nat_divides_antisym.

(** ** Properties of division *)

Local Definition nat_div_mod_unique_helper b q1 q2 r1 r2
  : r1 < b -> r2 < b -> q1 < q2 -> b * q1 + r1 <> b * q2 + r2.
Proof.
  intros H1 H2 H3 p.
  rewrite 2 (nat_add_comm (b * _)) in p.
  apply nat_moveL_nV in p.
  rewrite nat_sub_l_add_r in p; only 2: rapply nat_mul_l_monotone.
  rewrite <- nat_dist_sub_l in p.
  rewrite nat_add_comm in p.
  apply nat_moveR_nV in p.
  nrapply (snd (@leq_iff_not_gt b (r1 - r2))).
  2: exact (lt_leq_lt_trans _ H1).
  rewrite p.
  snrapply (leq_mul_r _ _ 0).
  by apply equiv_lt_lt_sub.
Defined.

(** Quotients and remainders are uniquely determined. *)
Definition nat_div_mod_unique d q1 q2 r1 r2
  : r1 < d -> r2 < d -> d * q1 + r1 = d * q2 + r2
    -> q1 = q2 /\ r1 = r2.
Proof.
  intros H1 H2 p.
  destruct (nat_trichotomy q1 q2) as [[q | q] | q].
  - contradiction (nat_div_mod_unique_helper d q1 q2 r1 r2).
  - split; trivial.
    destruct q. 
    by apply isinj_nat_add_l in p.
  - by contradiction (nat_div_mod_unique_helper d q2 q1 r2 r1).
Defined.

(** Divisibility by a positive natural number is a hprop. *)
Global Instance ishprop_nat_divides n m : 0 < n -> IsHProp (n | m).
Proof.
  intros H.
  apply hprop_allpath.
  intros [x p] [y q].
  rapply path_sigma_hprop.
  destruct H as [|n]; simpl.
  1: exact ((nat_mul_one_r _)^ @ p @ q^ @ nat_mul_one_r _).
  refine (fst (nat_div_mod_unique n.+1 x y 0 0 _ _ _)).
  lhs nrapply nat_add_zero_r.
  rhs nrapply nat_add_zero_r.
  rewrite 2 (nat_mul_comm n.+1).
  exact (p @ q^).
Defined.

(** This specifies the behaviour of [nat_div_mod_helper] when [u <= y]. *)
Definition nat_div_mod_helper_spec x y q u (H : u <= y)
  : let (q', u') := nat_div_mod x y q u in
     x + y.+1 * q + (y - u) = y.+1 * q' + (y - u') /\ u' <= y.
Proof.
  intros d r.
  induction x as [|x IHx] in y, q, u, H, d, r |- *; only 1: by split.
  destruct u as [|u].
  - destruct (IHx y q.+1 y _) as [p H'].
    split; trivial.
    rewrite <- p, nat_sub_zero_r, nat_sub_cancel, nat_add_zero_r.
    simpl.
    by rewrite nat_add_succ_r, <- 2 nat_add_assoc, nat_mul_succ_r.
  - destruct (IHx y q u _) as [p H'].
    split; trivial.
    rewrite <- p, 2 nat_add_succ_l, <- nat_add_succ_r.
    snrapply ap.
    rewrite nat_sub_succ_r.
    apply nat_succ_pred.
    rapply lt_moveL_nV.
Defined.

(** Division and modulo can be put in quotient-remainder form. *)
Definition nat_div_mod_spec x y : x = y * (x / y) + x mod y.
Proof.
  destruct y as [|y]; only 1: reflexivity.
  pose proof (p := fst (nat_div_mod_helper_spec x y 0 y _)).
  by rewrite nat_mul_zero_r, nat_sub_cancel, 2 nat_add_zero_r in p.
Defined.

Definition nat_div_mod_spec' x y : x - y * (x / y) = x mod y.
Proof.
  apply nat_moveR_nV.
  rhs nrapply nat_add_comm.
  apply nat_div_mod_spec.
Defined.

Definition nat_mod_lt_r' n m r : r < m -> n mod m < m.
Proof.
  intros H; destruct H; only 1: exact _.
  rapply (lt_leq_lt_trans (m:=m)).
Defined.
Hint Immediate nat_mod_lt_r' : typeclass_instances.

(** [n] modulo [m] is less than [m]. *)
Global Instance nat_mod_lt_r n m : 0 < m -> n mod m < m
  := nat_mod_lt_r' n m 0.

(** [n] modulo [m] is less than or equal to [m]. *)
Global Instance nat_mod_leq_l n m : n mod m <= n.
Proof.
  rewrite <- nat_div_mod_spec'.
  rapply leq_moveR_nV.
Defined.

(** Division is unique. *)
Definition nat_div_unique x y q r (H : r < y) (p : y * q + r = x) : q = x / y
  := fst (nat_div_mod_unique y q (x / y) r (x mod y) _ _ (p @ nat_div_mod_spec x y)).

(** Modulo is unique. *)
Definition nat_mod_unique x y q r (H : r < y) (p : y * q + r = x)  : r = x mod y
  := snd (nat_div_mod_unique y q (x / y) r (x mod y) _ _ (p @ nat_div_mod_spec x y)).

(** [0] divided by any number is [0]. *)
Definition nat_div_zero_l n : 0 / n = 0.
Proof.
  by induction n.
Defined.

(** [n] divided by [0] is [0] by convention. *)
Definition nat_div_zero_r n : n / 0 = 0 := idpath.

(** [n] divided by [1] is [n]. *)
Definition nat_div_one_r n : n / 1 = n.
Proof.
  lhs_V nrapply nat_mul_one_l.
  lhs_V nrapply nat_add_zero_r.
  symmetry; apply nat_div_mod_spec.
Defined.

(** [n] divided by [n] is [1]. *)
Definition nat_div_cancel n : 0 < n -> n / n = 1.
Proof.
  intros [|m _]; trivial; symmetry.
  nrapply (nat_div_unique _ _ _ 0); only 1: exact _.
  lhs nrapply nat_add_zero_r.
  nrapply nat_mul_one_r.
Defined.

(** [n * m] divided by [n] is [m]. *)
Definition nat_div_mul_cancel_l n m : 0 < n -> (n * m) / n = m.
Proof.
  intros H.
  symmetry.
  nrapply (nat_div_unique _ _ _ _ H).
  apply nat_add_zero_r.
Defined.

(** [n * m] divided by [n] is [m]. *)
Definition nat_div_mul_cancel_r n m : 0 < m -> (n * m) / m = n.
Proof.
  rewrite nat_mul_comm.
  apply nat_div_mul_cancel_l.
Defined.

(** When [d] divides [n] and [m], division distributes over addition. *)
Definition nat_div_dist n m d
  : 0 < d -> (d | n) -> (d | m) -> (n + m) / d = n / d + m / d.
Proof.
  intros H1 [x p] [y q].
  destruct p, q.
  rewrite <- nat_dist_r.
  by rewrite 3 nat_div_mul_cancel_r.
Defined.

(** [0] modulo [n] is [0]. *)
Definition nat_mod_zero_l n : 0 mod n = 0.
Proof.
  induction n; trivial.
  apply nat_sub_cancel.
Defined.

(** [n] modulo [0] is [n]. *)
Definition nat_mod_zero_r n : n mod 0 = n := idpath.

(** TODO: generalise for all small n *)
Definition nat_mod_one_l n : 1 < n -> 1 mod n = 1.
Proof.
  intros H.
  destruct H; trivial.
  destruct m.
  1: contradiction (not_lt_zero_r _ H).
  cbn; clear H.
  by induction m.
Defined.

(** [n] modulo [1] is [0]. *)
Definition nat_mod_one_r n : n mod 1 = 0.
Proof.
  by induction n.
Defined.

(** If [m] divides [n], then [n mod m = 0]. *)
Definition nat_mod_divides n m : 0 < m -> (m | n) -> n mod m = 0.
Proof.
  intros H [x p].
  destruct p.
  lhs_V nrapply nat_div_mod_spec'.
  pose (nat_div_cancel m H).
  rewrite nat_div_mul_cancel_r; only 2: exact _.
  apply nat_moveR_nV, nat_mul_comm.
Defined.

(** [n] modulo [n] is [0]. *)
Definition nat_mod_cancel n : n mod n = 0.
Proof.
  destruct n; trivial.
  symmetry.
  snrapply (nat_mod_unique _ _ 1); only 1: exact _.
  lhs nrapply nat_add_zero_r.
  nrapply nat_mul_one_r.
Defined.

(** ** Greatest Common Divisor *)

(** The greatest common divisor of [0] and a number is the number itself. *)
Definition nat_gcd_zero_l n : nat_gcd 0 n = n := idpath.

(** The greatest common divisor of a number and [0] is the number itself. *)
Definition nat_gcd_zero_r n : nat_gcd n 0 = n.
Proof.
  induction n; simpl; only 1: reflexivity.
  by rewrite nat_sub_cancel.
Defined.

(** The greatest common divisor of [1] and any number is [1]. *)
Definition nat_gcd_one_l n : nat_gcd 1 n = 1 := idpath.

(** The greatest common divisor of any number and [1] is [1]. *)
Definition nat_gcd_one_r n : nat_gcd n 1 = 1.
Proof.
  destruct n; trivial.
  simpl.
  destruct n; trivial.
  rewrite nat_sub_succ_l; only 2: exact _.
  by rewrite nat_sub_cancel.
Defined.

(** Idempotency. *)
Definition nat_gcd_idem n : nat_gcd n n = n.
Proof.
  induction n.
  1: reflexivity.
  unfold nat_gcd; fold nat_gcd.
  by rewrite nat_mod_cancel.
Defined.

(** We can prove that the greatest common divisor of [n] and [m] divides both [n] and [m]. This proof requires strong induction. *)
Definition nat_divides_l_gcd n m : (nat_gcd n m | n) /\ (nat_gcd n m | m).
Proof.
  revert n m; snrapply nat_ind_strong; intros n IHn m.
  destruct n.
  1: split; exact _.
  destruct (IHn (m mod n.+1) _ n.+1) as [H1 H2].
  unfold nat_gcd; fold nat_gcd.
  set (n' := n.+1) in *.
  split; only 1: exact H2.
  set (r := m mod n'); rewrite (nat_div_mod_spec m n'); unfold r; clear r.
  exact _.
Defined.

(** The greatest common divisor of [n] and [m] divides [n]. *)
Global Instance nat_divides_l_gcd_l n m : (nat_gcd n m | n)
  := fst (nat_divides_l_gcd n m).

(** The greatest common divisor of [n] and [m] divides [m]. *)
Global Instance divides_l_nat_gcd_r n m : (nat_gcd n m | m)
  := snd (nat_divides_l_gcd n m).
  
(** We can prove that any common divisor of [n] and [m] divides the greatest common divisor of [n] and [m]. It is in that sense the greatest. *)
Global Instance nat_divides_r_gcd n m p : (p | n) -> (p | m) -> (p | nat_gcd n m).
Proof.
  revert n m p; snrapply nat_ind_strong; intros n IHn m p H1 H2.
  destruct n; only 1: exact _.
  unfold nat_gcd; fold nat_gcd.
  apply IHn; only 1,3: exact _.
  rewrite (nat_div_mod_spec m n.+1) in H2.
  apply nat_divides_add_r in H2; exact _.
Defined.

Definition nat_divides_r_iff_divides_r_gcd n m p
  : (p | n) * (p | m) <-> (p | nat_gcd n m).
Proof.
  split; [intros [H1 H2] | intros H; split]; exact _.
Defined.

(** If [p] is divisible by all common divisors of [n] and [m], and [p] is also a common divisor, then it must necesserily be equal to the greatest common divisor. *)
Definition nat_gcd_unique n m p
  (H : forall q, (q | n) -> (q | m) -> (q | p))
  : (p | n) -> (p | m) -> nat_gcd n m = p.
Proof.
  intros H1 H2.
  rapply nat_divides_antisym.
Defined.

(** As a corollary of uniquness, we get that the greatest common divisor operation is commutative. *)
Definition nat_gcd_comm n m : nat_gcd n m = nat_gcd m n.
Proof.
  rapply nat_gcd_unique.
Defined.

(** [nat_gcd] is associative. *)
Definition nat_gcd_assoc n m k : nat_gcd n (nat_gcd m k) = nat_gcd (nat_gcd n m) k.
Proof.
  nrapply nat_gcd_unique.
  - intros q H1 H2.
    rapply nat_divides_r_gcd. 
  - rapply (nat_divides_trans (nat_divides_l_gcd_l _ _)).
  - apply nat_divides_r_gcd; rapply nat_divides_trans.
Defined.

(** If [nat_gcd n m] is [0], then [n] must also be [0]. *)
Definition nat_gcd_is_zero_l n m : nat_gcd n m = 0 -> n = 0.
Proof.
  intros H.
  generalize (nat_divides_l_gcd_l n m).
  rewrite H.
  intros [x p].
  exact (p^ @ nat_mul_zero_r _).
Defined.

(** If [nat_gcd n m] is [0], then [m] must also be [0]. *)
Definition nat_gcd_is_zero_r n m : nat_gcd n m = 0 -> m = 0.
Proof.
  rewrite nat_gcd_comm.
  apply nat_gcd_is_zero_l.
Defined.

(** [nat_gcd n m] is [0] if and only if both [n] and [m] are [0]. *)
Definition nat_gcd_zero_iff_zero n m : nat_gcd n m = 0 <-> n = 0 /\ m = 0.
Proof.
  split.
  - split.
    + by apply (nat_gcd_is_zero_l _ m).
    + by apply (nat_gcd_is_zero_r n).
  - intros [-> ->].
    reflexivity.
Defined.

(** [nat_gcd] is positive for positive inputs. *)
Global Instance nat_gcd_pos n m : 0 < n -> 0 < m -> 0 < nat_gcd n m.
Proof.
  intros H1 H2.
  apply lt_iff_not_geq.
  intros H3; hnf in H3.
  apply path_zero_leq_zero_r in H3.
  apply nat_gcd_zero_iff_zero in H3.
  destruct H3 as [->].
  contradiction (not_lt_zero_r _ H1).
Defined.
