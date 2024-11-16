Require Import Basics.Overture Basics.Tactics Basics.Trunc Basics.Classes
  Basics.PathGroupoids Basics.Equivalences Types.Sigma Spaces.Nat.Core
  Basics.Decidable Basics.Iff Types.Prod List.Theory Types.Sum Types.Arrow.

Local Set Universe Minimization ToSet.
Local Open Scope nat_scope.

(** * Division of natural numbers *)

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

(** Multiplication is monotone with respect to divisibility. *)
Global Instance nat_divides_mul_monotone n m l p
  : (n | m) -> (l | p) -> (n * l | m * p).
Proof.
  intros [x r] [y q].
  exists (x * y).
  destruct r, q.
  lhs nrapply nat_mul_assoc.
  rhs nrapply nat_mul_assoc.
  nrapply (ap (fun x => nat_mul x _)).
  lhs_V nrapply nat_mul_assoc.
  rhs_V nrapply nat_mul_assoc.
  nrapply ap.
  apply nat_mul_comm.
Defined.

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

(** The divisor is greater than zero when the divident is greater than zero. *)
Definition gt_zero_divides n m (d : (n | m)) (gt0 : 0 < m)
  : 0 < n.
Proof.
  destruct d as [d H].
  destruct H.
  destruct (nat_zero_or_gt_zero n) as [z | s].
  2: exact s.
  (* The remaining case is impossible. *)
  destruct z; cbn in gt0.
  rewrite nat_mul_zero_r in gt0.
  exact gt0.
Defined.

(** Divisibility implies that the divisor is less than or equal to the dividend. *)
Definition leq_divides n m : 0 < m -> (n | m) -> n <= m.
Proof.
  intros H1 [x p].
  destruct p, x.
  1: contradiction (not_lt_zero_r _ H1).
  rapply (leq_mul_l _ _ 0).
Defined.

(** The divisor is strictly less than the dividend when the other factor is greater than one. *)
Definition lt_divides n m (d : (n | m)) (gt0 : 0 < m) (gt1 : 1 < d.1)
  : n < m.
Proof.
  rewrite <- d.2.
  snrapply (lt_leq_lt_trans (m:=1*n)).
  1: rapply (leq_mul_l _ _ 0).
  srapply (nat_mul_r_strictly_monotone (l:=0)).
  rapply (gt_zero_divides n m).
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

(** If [n] divides [m], then the other factor also divides [m]. *)
Global Instance divides_divisor n m (H : (n | m)) : (H.1 | m).
Proof.
  exists n.
  lhs nrapply nat_mul_comm.
  exact H.2.
Defined.

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

Definition nat_div_mod_spec'' x y : x - x mod y = y * (x / y).
Proof.
  apply nat_moveR_nV.
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
Definition nat_div_unique x y q r (H : r < y) (p : y * q + r = x) : x / y = q
  := fst (nat_div_mod_unique y (x / y) q (x mod y) r _ _ (p @ nat_div_mod_spec x y)^).

(** Modulo is unique. *)
Definition nat_mod_unique x y q r (H : r < y) (p : y * q + r = x) : x mod y = r
  := snd (nat_div_mod_unique y (x / y) q (x mod y) r _ _ (p @ nat_div_mod_spec x y)^).

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
  intros [|m _]; trivial.
  nrapply (nat_div_unique _ _ _ 0); only 1: exact _.
  lhs nrapply nat_add_zero_r.
  nrapply nat_mul_one_r.
Defined.

(** A number divided by a larger number is 0. *)
Definition nat_div_lt n m : n < m -> n / m = 0.
Proof.
  intros H.
  snrapply (nat_div_unique _ _ _ _ H).
  by rewrite nat_mul_zero_r, nat_add_zero_l.
Defined.

(** [n * m] divided by [n] is [m]. *)
Definition nat_div_mul_cancel_l n m : 0 < n -> (n * m) / n = m.
Proof.
  intros H.
  nrapply (nat_div_unique _ _ _ _ H).
  apply nat_add_zero_r.
Defined.

(** [n * m] divided by [n] is [m]. *)
Definition nat_div_mul_cancel_r n m : 0 < m -> (n * m) / m = n.
Proof.
  rewrite nat_mul_comm.
  apply nat_div_mul_cancel_l.
Defined.

(** More generally, [n * m + k] divided by [n] is [m + k / n]. *)
Definition nat_div_mul_add_cancel_l n m k : 0 < n -> (n * m + k) / n = m + k / n.
Proof.
  intros H.
  rapply (nat_div_unique _ _ _ (k mod n) _).
  rewrite nat_dist_l.
  lhs_V nrapply nat_add_assoc.
  f_ap.
  symmetry; apply nat_div_mod_spec.
Defined.

Definition nat_div_mul_add_cancel_r n m k : 0 < m -> (n * m + k) / m = n + k / m.
Proof.
  rewrite nat_mul_comm.
  apply nat_div_mul_add_cancel_l.
Defined.

(** If [k] is positive, then multiplication on the left is injective; that is, if [k * m = k * n], then [m = n]. *)
Definition isinj_nat_mul_l k : 0 < k -> IsInjective (nat_mul k).
Proof.
  intros kp m n p.
  lhs_V rapply (nat_div_mul_cancel_l k).
  rhs_V rapply (nat_div_mul_cancel_l k).
  exact (ap (fun x => x / k) p).
Defined.

(** If [k] is positive, then multiplication on the right is injective; that is, if [m * k = n * k], then [m = n]. *)
Definition isinj_nat_mul_r k : 0 < k -> IsInjective (fun n => nat_mul n k).
Proof.
  intros kp m n p.
  lhs_V rapply (nat_div_mul_cancel_r _ k).
  rhs_V rapply (nat_div_mul_cancel_r _ k).
  exact (ap (fun x => x / k) p).
Defined.

(** When [d] divides one of the summands, division distributes over addition. *)
Definition nat_div_dist n m d
  : (d | n) -> (n + m) / d = n / d + m / d.
Proof.
  destruct d.
  1: reflexivity.
  intros [x []].
  rewrite nat_div_mul_cancel_r. 2: exact _.
  rapply nat_div_mul_add_cancel_r.
Defined.

Definition nat_div_dist' n m d
  : (d | m) -> (n + m) / d = n / d + m / d.
Proof.
  intros H.
  rewrite (nat_add_comm n m).
  rhs_V nrapply nat_add_comm.
  rapply nat_div_dist.
Defined.

(** In general, [n * (m / n)] is less than or equal to [m]. *)
Definition nat_leq_mul_div_l n m
  : n * (m / n) <= m.
Proof.
  set (tmp := n * (m / n));
    rewrite (nat_div_mod_spec m n);
    unfold tmp; clear tmp.
  exact _.
Defined.

(** When [n] divides [m], they are equal. *)
Definition nat_mul_div_cancel_r n m
  : (n | m) -> (m / n) * n = m.
Proof.
  destruct n.
  { intros [k []]. cbn. symmetry; apply nat_mul_zero_r. }
  intros [k []].
  f_ap.
  rapply nat_div_mul_cancel_r.
Defined.

Definition nat_mul_div_cancel_l n m
  : (n | m) -> n * (m / n) = m.
Proof.
  rewrite nat_mul_comm.
  apply nat_mul_div_cancel_r.
Defined.

(** Division by non-zero [k] is strictly monotone if [k] divides the larger number. *)
Definition nat_div_strictly_monotone_r {n m l} k
  : l < k -> n < m -> (k | m) -> n / k < m / k.
Proof.
  intros lk nm km.
  apply gt_iff_not_leq.
  intro mknk.
  apply (@gt_iff_not_leq m n); only 1: apply nm.
  rewrite <- (nat_mul_div_cancel_l k m km).
  nrapply (leq_trans (y:=k * (n / k))).
  - rapply nat_mul_l_monotone.
  - apply nat_leq_mul_div_l.
Defined.

(** [0] modulo [n] is [0]. *)
Definition nat_mod_zero_l n : 0 mod n = 0.
Proof.
  induction n; trivial.
  apply nat_sub_cancel.
Defined.

(** [n] modulo [0] is [n]. *)
Definition nat_mod_zero_r n : n mod 0 = n := idpath.

Definition nat_mod_lt n k : k < n -> k mod n = k.
Proof.
  intros H.
  lhs_V nrapply nat_div_mod_spec'.
  rewrite nat_div_lt.
  - rewrite nat_mul_zero_r.
    apply nat_sub_zero_r.
  - exact H.
Defined.

(** [n] modulo [1] is [0]. *)
Definition nat_mod_one_r n : n mod 1 = 0.
Proof.
  by induction n.
Defined.

(** If [m] divides [n], then [n mod m = 0]. *)
Definition nat_mod_divides n m : (m | n) -> n mod m = 0.
Proof.
  intros [x p].
  destruct p.
  destruct m.
  { simpl. apply nat_mul_zero_r. }
  lhs_V nrapply nat_div_mod_spec'.
  rewrite nat_div_mul_cancel_r; only 2: exact _.
  apply nat_moveR_nV, nat_mul_comm.
Defined.

(** [n mod m = 0] iff [m] divides [n]. *)
Definition nat_mod_iff_divides n m : n mod m = 0 <-> (m | n) .
Proof.
  split.
  2: exact (nat_mod_divides _ _).
  intros p.
  exists (n / m).
  rewrite nat_mul_comm.
  lhs_V nrapply nat_add_zero_r.
  rewrite <- p.
  symmetry.
  nrapply nat_div_mod_spec.
Defined.

(** Divisibility is therefore decidable. *)
Global Instance decidable_nat_divides n m : Decidable (n | m).
Proof.
  nrapply decidable_iff.
  1: apply nat_mod_iff_divides.
  exact _.
Defined.

(** [n] modulo [n] is [0]. *)
Definition nat_mod_cancel n : n mod n = 0.
Proof.
  destruct n; trivial.
  snrapply (nat_mod_unique _ _ 1); only 1: exact _.
  lhs nrapply nat_add_zero_r.
  nrapply nat_mul_one_r.
Defined.

(** A number can be corrected so that it is divisible by subtracting the modulo. *)
Global Instance nat_divides_sub_mod n m : (n | m - m mod n).
Proof.
  rewrite nat_div_mod_spec''.
  exact _.
Defined.

(** ** Further Properties of division and modulo *)

(** We can cancel common factors on the left in a division. *)
Definition nat_div_cancel_mul_l n m k
  : 0 < k -> (k * n) / (k * m) = n / m.
Proof.
  intro kp.
  destruct (nat_zero_or_gt_zero m) as [[] | mp].
  1: by rewrite nat_mul_zero_r.
  nrapply (nat_div_unique _ _ _ (k * (n mod m))).
  1: rapply nat_mul_l_strictly_monotone.
  rewrite <- nat_mul_assoc.
  rewrite <- nat_dist_l.
  apply ap.
  symmetry; apply nat_div_mod_spec.
Defined.

(** We can cancel common factors on the right in a division. *)
Definition nat_div_cancel_mul_r n m k
  : 0 < k -> (n * k) / (m * k) = n / m.
Proof.
  rewrite 2 (nat_mul_comm _ k).
  nrapply nat_div_cancel_mul_l.
Defined.

(** We can swap the order of division and multiplication on the left under certain conditions. *)
Definition nat_div_mul_l n m k : (m | n) -> k * (n / m) = (k * n) / m.
Proof.
  intros H.
  destruct (nat_zero_or_gt_zero m) as [[] | mp].
  1: snrapply nat_mul_zero_r.
  rapply (nat_div_unique _ _ _ 0 _ _)^.
  lhs nrapply nat_add_zero_r.
  lhs nrapply nat_mul_assoc.
  lhs nrapply (ap (fun x => x * _)).
  1: nrapply nat_mul_comm.
  lhs_V nrapply nat_mul_assoc.
  snrapply ap.
  lhs_V nrapply nat_add_zero_r.
  rhs nrapply (nat_div_mod_spec n m).
  snrapply ap.
  symmetry.
  rapply nat_mod_divides.
Defined.

(** We can swap the order of division and multiplication on the right under certain conditions. *)
Definition nat_div_mul_r n m k : (m | n) -> (n / m) * k = (n * k) / m.
Proof.
  rewrite 2 (nat_mul_comm _ k).
  snrapply nat_div_mul_l.
Defined.

Definition nat_div_sub_mod n m : n / m = (n - n mod m) / m.
Proof.
  destruct (nat_zero_or_gt_zero m) as [[] | mp].
  1: reflexivity.
  symmetry.
  rewrite nat_div_mod_spec''.
  rapply nat_div_mul_cancel_l.
Defined.

(** Dividing a quotient is the same as dividing by the product of the divisors. *)
Definition nat_div_div_l n m k : (n / m) / k = n / (m * k).
Proof.
  destruct (nat_zero_or_gt_zero k) as [[] | kp].
  1: by rewrite nat_mul_zero_r.
  destruct (nat_zero_or_gt_zero m) as [[] | mp].
  1: snrapply nat_div_zero_l.
  apply nat_div_unique with (r := (n mod (m * k)) / m).
  { apply (lt_lt_leq_trans (m:=(m * k)/m)).
    - rapply nat_div_strictly_monotone_r.
      nrapply (nat_mod_lt_r' _ _ 0 _).
      exact (nat_mul_strictly_monotone mp kp).
    - by rewrite nat_div_mul_cancel_l. }
  transitivity ((m * (k * (n / (m * k)))) / m + (n mod (m * k)) / m).
  - f_ap.
    symmetry; rapply nat_div_mul_cancel_l.
  - rewrite nat_mul_assoc.
    lhs_V nrapply nat_div_dist.
    1: exact _.
    apply (ap (fun x => x / m)).
    symmetry; apply nat_div_mod_spec.
Defined.

(** Dividing a number by a quotient is the same as dividing the product of the number with the denominator of the quotient by the numerator of the quotient. *)
Definition nat_div_div_r n m k : (k | m) -> n / (m / k) = (n * k) / m.
Proof. 
  intros [d r].
  destruct (nat_zero_or_gt_zero k) as [[] | kp].
  1: by rewrite nat_mul_zero_r, nat_div_zero_l.
  destruct r.
  rhs nrapply nat_div_cancel_mul_r.
  2: exact _.
  apply ap.
  rapply nat_div_mul_cancel_r.
Defined.

(** A variant of [nat_div_div_r] without the divisibility assumption, by modifying [m] to become divisible. *)
Definition nat_div_div_r' n m k : n / (m / k) = (n * k) / (m - m mod k).
Proof.
  rewrite (nat_div_sub_mod m k).
  rapply nat_div_div_r.
Defined.

(** We can cancel common factors on the left in a modulo. *)
Definition nat_mod_mul_l n m k
  : (k * n) mod (k * m) = k * (n mod m).
Proof.
  destruct (nat_zero_or_gt_zero k) as [[] | kp].
  1: reflexivity.
  destruct (nat_zero_or_gt_zero m) as [[] | mp].
  1: by rewrite nat_mul_zero_r.
  apply (nat_mod_unique _ _ (n / m)).
  1: rapply nat_mul_l_strictly_monotone.
  rewrite <- nat_mul_assoc.
  rewrite <- nat_dist_l.
  apply ap.
  symmetry; apply nat_div_mod_spec.
Defined.

(** We can cancel common factors on the right in a modulo. *)
Definition nat_mod_mul_r n m k
  : (n * k) mod (m * k) = (n mod m) * k.
Proof.
  rewrite 3 (nat_mul_comm _ k).
  nrapply nat_mod_mul_l.
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

Definition nat_gcd_l_add_r_mul n m k : nat_gcd (n + k * m) m = nat_gcd n m.
Proof.
  rapply nat_gcd_unique.
  intros q H1 H2.
  rapply nat_divides_r_gcd.
  rapply (nat_divides_add_l _ _ (k * m)).
Defined.

Definition nat_gcd_r_add_r_mul n m k : nat_gcd n (m + k * n) = nat_gcd n m.
Proof.
  lhs nrapply nat_gcd_comm.
  rhs nrapply nat_gcd_comm.
  nrapply nat_gcd_l_add_r_mul.
Defined.

Definition nat_gcd_l_add_r n m : nat_gcd (n + m) m = nat_gcd n m.
Proof.
  rhs_V nrapply (nat_gcd_l_add_r_mul n m 1).
  by rewrite nat_mul_one_l.
Defined.

Definition nat_gcd_r_add_r n m : nat_gcd n (m + n) = nat_gcd n m.
Proof.
  lhs nrapply nat_gcd_comm.
  rhs nrapply nat_gcd_comm.
  nrapply nat_gcd_l_add_r.
Defined.

Definition nat_gcd_l_sub n m : m <= n -> nat_gcd (n - m) m = nat_gcd n m.
Proof.
  intros H.
  lhs_V nrapply nat_gcd_l_add_r.
  by rewrite (nat_add_sub_l_cancel H).
Defined.

Definition nat_gcd_r_sub n m : n <= m -> nat_gcd n (m - n) = nat_gcd n m.
Proof.
  intros H.
  lhs nrapply nat_gcd_comm.
  rhs nrapply nat_gcd_comm.
  rapply nat_gcd_l_sub.
Defined.

(** ** Bezout's Identity *)

(** Bezout's identity states that for any two numbers [n] and [m], their greatest common divisor can be written as a linear combination of [n] and [m]. This is easy to state for the integers, however since we are working with the natural numbers, we need to be more careful. This is why we write the linear combination as [a * n = d + b * m] rather than the usual [a * n + b * m = d]. *)

(** We define a predicate for triples of integers satisfying Bezout's identity. *)
Definition NatBezout n m d : Type0
  := exists a b, a * n = d + b * m.
Existing Class NatBezout.

Global Instance nat_bezout_refl_l n k : NatBezout n k n.
Proof.
  by exists 1, 0.
Defined.

(** If [a * n = 1 + b * m], then the gcd of [n] and [m] is [1]. *)
Definition nat_bezout_coprime n m : NatBezout n m 1 -> nat_gcd n m = 1.
Proof.
  intros [a [b p]].
  rapply nat_gcd_unique.
  intros q H1 H2.
  rapply (nat_divides_add_l _ _ (b * m)).
  destruct p; exact _.
Defined.

Definition nat_bezout_comm n m d
  : 0 < m -> NatBezout n m d -> NatBezout m n d.
Proof.
  intros H [a [b p]].
  destruct (@equiv_leq_lt_or_eq 0 a _) as [|q].
  - exists (n * a.+1 * b.+1 - b), (m * a.+1 * b.+1 - a).
    rewrite 2 nat_dist_sub_r.
    apply nat_moveR_nV.
    rewrite <- nat_add_comm, nat_add_assoc, <- (nat_add_comm d).
    rewrite <- nat_sub_l_add_r.
    2: { apply nat_mul_r_monotone.
      rewrite 2 nat_mul_succ_r.
      nrapply (leq_trans _ (leq_add_l _ _)).
      rapply (leq_trans _ (leq_add_r _ _)). }
    apply nat_moveL_nV.
    rewrite nat_add_comm.
    snrapply (ap011 nat_add p).
    lhs nrapply nat_mul_comm.
    rhs_V nrapply nat_mul_assoc.
    rhs_V nrapply nat_mul_assoc.
    snrapply ap.
    lhs_V nrapply nat_mul_assoc.
    rhs nrapply nat_mul_assoc.
    apply nat_mul_comm.
  - destruct q.
    exists 0, 0.
    rewrite 2 nat_mul_zero_l, nat_add_zero_r in *.
    symmetry in p; symmetry.
    apply equiv_nat_add_zero in p.
    by destruct p.
Defined.
Hint Immediate nat_bezout_comm : typeclass_instances.

Global Instance nat_bezout_pos_l n m : 0 < n -> NatBezout n m (nat_gcd n m).
Proof.
  pose (k := n + m); assert (p : n + m = k) by reflexivity; clearbody k.
  revert k n m p; snrapply nat_ind_strong; hnf; intros k IHk n m q H.
  (** Given a sum [n + m], we can always find another pair [n' + m'] equal to that sum such that [n' < m']. This extra hypothesis lets us prove the statement more directly. *)
  assert (H' : forall n' m', n + m = n' + m' -> 0 < n' -> n' < m'
    -> NatBezout n' m' (nat_gcd n' m')).
  { intros n' m' p H1 H2; destruct q.
    assert (m' < n + m) by (rewrite p; change (0 + m' < n' + m'); exact _).
    destruct (IHk m' _ n' (m' - n') (nat_add_sub_r_cancel _) _) as [a [b r]].
    exists (a + b), b.
    rewrite nat_dist_r, r, nat_dist_sub_l, <- nat_add_assoc.
    rewrite nat_add_sub_l_cancel; only 2: rapply nat_mul_l_monotone.
    snrapply (ap (fun x => x + _)).
    rapply nat_gcd_r_sub. }
  destruct (nat_trichotomy n m) as [[l | p] | r].
  - by apply H'.
  - destruct p.
    rewrite nat_gcd_idem; exact _.
  - destruct (@equiv_leq_lt_or_eq 0 m _).
    + rewrite nat_gcd_comm.
      rapply nat_bezout_comm.
      rapply H'.
      apply nat_add_comm.
    + destruct p.
      rewrite nat_gcd_zero_r; exact _.
Defined.

(** For strictly positive numbers, we have Bezout's identity in both directions. *)
Definition nat_bezout_pos n m
  : 0 < n -> 0 < m
  -> NatBezout n m (nat_gcd n m) /\ NatBezout m n (nat_gcd n m).
Proof.
  intros H1 H2; split; [| apply nat_bezout_comm]; exact _.
Defined.

(** For arbitrary natural numbers, we have Bezout's identity in at least one direction. *)
Definition nat_bezout n m
  : NatBezout n m (nat_gcd n m) + NatBezout m n (nat_gcd n m).
Proof.
  destruct n; [ right | left ]; exact _.
Defined.

(** ** Prime Numbers *)

(** A prime number is a number greater than [1] that is only divisible by [1] and itself. *)
Class IsPrime (n : nat) : Type0 := {
  gt_one_isprime :: 1 < n;
  isprime : forall m, (m | n) -> (m = 1) + (m = n);
}.

Definition issig_IsPrime n : _ <~> IsPrime n := ltac:(issig).

Global Instance ishprop_isprime `{Funext} n : IsHProp (IsPrime n).
Proof.
  nrapply istrunc_equiv_istrunc.
  1: apply issig_IsPrime.
  rapply istrunc_sigma.
  intros H1.
  snrapply istrunc_forall.
  intros m.
  snrapply istrunc_forall.
  intros d.
  rapply ishprop_sum.
  intros p q.
  nrapply (snd neq_iff_lt_or_gt _ (p^ @ q)).
  by left.
Defined.

(** [0] is not a prime number. *)
Definition not_isprime_zero : ~ IsPrime 0.
Proof.
  intros H.
  rapply not_lt_zero_r.
Defined.

(** [1] is not a prime number. *)
Definition not_isprime_one : ~ IsPrime 1.
Proof.
  intros H.
  rapply (lt_irrefl 1).
Defined.

(** Being prime is a decidable property. We give an inefficient procedure for determining primality. More efficient procedures can be given, but for proofs this suffices. *)
Global Instance decidable_isprime@{} n : Decidable (IsPrime n).
Proof.
  (** First we begin by discarding the [n = 0] case as we can easily prove that [0] is not prime. *)
  destruct n.
  1: right; apply not_isprime_zero.
  (** Next, we rewrite [IsPrime n.+1] as the equivalent sigma type. *)
  nrapply decidable_equiv'.
  1: nrapply issig_IsPrime.
  (** The condition in the first component in [IsPrime] is clearly decidable, so we can proceed to the second component. *)
  nrapply decidable_equiv'.
  1: exact (equiv_sigma_prod0 _ _)^-1%equiv.
  snrapply decidable_prod.
  1: exact _.
  (** In order to show that this [forall] is decidable, we will exhibit it as a [for_all] statement over a given list. The predicate will be the conclusion we wish to reach here, and the list will consist of all numbers with a condition equivalent to the divisibility condition. *)
  pose (P := fun m => ((m = 1) + (m = n.+1))%type : Type0).
  pose (l := list_filter (seq n.+2) (fun x => (x | n.+1)) _).
  rapply (decidable_iff (A := for_all P l)).
  split.
  - intros Pl x d.
    apply inlist_for_all with l x in Pl.
    1: exact Pl.
    apply inlist_filter.
    split; only 2: assumption.
    apply inlist_seq.
    apply leq_divides in d.
    1,2: exact _.
  - intros H.
    apply for_all_inlist.
    intros x H'.
    apply inlist_filter in H'.
    destruct H' as [p H'].
    apply inlist_seq in p.
    rapply H.
Defined.

(** We can show that the first 8 primes are prime as expected. *)
Global Instance isprime_2 : IsPrime 2 := ltac:(decide).
Global Instance isprime_3 : IsPrime 3 := ltac:(decide).
Global Instance isprime_5 : IsPrime 5 := ltac:(decide).
Global Instance isprime_7 : IsPrime 7 := ltac:(decide).
Global Instance isprime_11 : IsPrime 11 := ltac:(decide).
Global Instance isprime_13 : IsPrime 13 := ltac:(decide).
Global Instance isprime_17 : IsPrime 17 := ltac:(decide).
Global Instance isprime_19 : IsPrime 19 := ltac:(decide).

(** Similarly, we can see that other natural numbers are not prime. *)
Definition not_isprime_0 : not (IsPrime 0) := ltac:(decide).
Definition not_isprime_1 : not (IsPrime 1) := ltac:(decide).
Definition not_isprime_4 : not (IsPrime 4) := ltac:(decide).

(** We can define the type of prime numbers as a subtype of natural numbers. *)
Definition Prime : Type0 := {n : nat & IsPrime n}.

Coercion nat_of_prime (p : Prime) : nat := p.1.
Global Instance isprime_prime (p : Prime) : IsPrime p := p.2.

Global Instance lt_zero_prime (p : Prime) : 0 < p
  := lt_trans _ gt_one_isprime.

(** A prime [p] is coprime to a natural number [n] iff [p] does not divide [n]. *)
Definition nat_coprime_iff_not_divides (p : Prime) n
  : nat_gcd p n = 1 <-> ~ (p | n).
Proof.
  split.
  - intros q [d r].
    destruct r.
    rewrite (nat_gcd_r_add_r_mul p 0) in q.
    rewrite nat_gcd_zero_r in q.
    apply (@neq_iff_lt_or_gt p 1).
    1: right; exact _.
    exact q.
  - intros nd.
    rapply nat_gcd_unique.
    intros q H1 H2.
    apply isprime in H1.
    destruct H1 as [H1|H1].
    + destruct H1; exact _.
    + destruct H1; contradiction.
Defined.

(** When a prime number divides a multiple, then the prime must divide one of the factors. *)
Definition nat_divides_prime_l (p : Prime) n m
  : (p | n * m) -> (p | n) + (p | m).
Proof.
  intros d.
  destruct (dec (p | n)) as [H|H].
  1: by left.
  right.
  apply nat_coprime_iff_not_divides in H.
  destruct (nat_bezout_pos_l p n _) as [x [y q]].
  destruct H^; clear H.
  destruct d as [d r].
  exists (x * m - y * d).
  lhs nrapply nat_dist_sub_r.
  rewrite <- 2 nat_mul_assoc.
  rewrite <- (nat_mul_comm p).
  destruct r^; clear r.
  rewrite 2 nat_mul_assoc.
  lhs_V nrapply nat_dist_sub_r.
  rhs_V nrapply nat_mul_one_l.
  apply (ap (fun x => nat_mul x m)).
  apply nat_moveR_nV.
  exact q.
Defined.

(** ** Composite Numbers *)

(** A natural number larger than [1] is composite if it has a divisor other than [1] and itself. *)
Class IsComposite n : Type0
  := iscomposite : exists a, 1 < a < n /\ (a | n).

Definition gt_1_iscomposite@{} n : IsComposite n -> 1 < n.
Proof.
  intros [a [[H1 H2] H3]].
  exact _.
Defined.
Hint Immediate gt_1_iscomposite : typeclass_instances.

(** Being composite is a decidable property. *)
Global Instance decidable_iscomposite@{} n : Decidable (IsComposite n).
Proof.
  unfold IsComposite.
  rapply (decidable_exists_nat n).
  intros k c.
  exact (snd (fst c)).
Defined.

(** For a number larger than [1], being prime is equivalent to not being composite. *)
Definition isprime_iff_not_iscomposite@{} n
  : IsPrime n <-> 1 < n /\ ~ IsComposite n.
Proof.
  split.
  - intros H.
    split; only 1: exact _.
    intros [a [[H2 H3] H4]].
    apply isprime in H4.
    destruct H4 as [H4|H4]; destruct H4; exact (lt_irrefl _ _).
  - intros [H1 H].
    rapply Build_IsPrime.
    intros m d.
    destruct (dec (1 < d.1)) as [H2|H2].
    + pose proof (divides_divisor _ _ d) as d'.
      apply leq_divides in d'.
      2: exact _.
      apply equiv_leq_lt_or_eq in d'.
      destruct d' as [d'|d'].
      * assert (H' : IsComposite n).
        { exists d.1.
          split; only 1: split; exact _. }
          contradiction H.
      * destruct d as [d r].
        simpl in *.
        destruct d'.
         left.
         rewrite <- nat_div_cancel with d.
         2: exact _.
         rewrite <- nat_div_mul_cancel_l with d m.
         2: exact _.
         by apply (ap (fun x => x / d)).
    + apply geq_iff_not_lt in H2.
      destruct d as [d r].
      simpl in *; hnf in H2.
      destruct d.
      { rewrite nat_mul_zero_l in r.
        destruct n.
        1: contradiction (not_lt_zero_r _ H1).
        contradiction (neq_nat_zero_succ _ r). }
      destruct d.
      { rewrite nat_mul_one_l in r.
        by right. }
      apply leq_pred' in H2.
      contradiction (not_lt_zero_r d).
Defined.

(** And since [IsComposite] is decidable, we can show that being not prime is equivalent to being composite. *)
Definition not_isprime_iff_iscomposite@{} n
  : 1 < n /\ ~ IsPrime n <-> IsComposite n.
Proof.
  nrapply iff_compose.
  - nrapply iff_functor_prod.
    1: nrapply iff_refl.
    nrapply iff_compose.
    + apply iff_not.
      rapply isprime_iff_not_iscomposite.
    + rapply iff_not_prod.
  - nrapply iff_compose.
    1: nrapply sum_distrib_l.
    nrapply iff_compose.
    + nrapply iff_functor_sum.
      1: apply iff_contradiction.
      nrapply iff_functor_prod.
      1: nrapply iff_refl.
      rapply iff_stable.
    + nrapply iff_compose.
      1: rapply sum_empty_l.
      split; only 1: exact snd.
      intros H; split; only 2: exact H.
      exact _.
Defined.

(** ** Fundamental theorem of arithmetic *)

(** Every natural number greater than [1] has a prime divisor. *)
Definition exists_prime_divisor@{} n
  : 1 < n -> exists (p : Prime), (p | n).
Proof.
  revert n; snrapply nat_ind_strong; hnf; intros n IHn H.
  destruct (dec (IsPrime n)) as [x|x].
  1: exists (_; x); exact _.
  pose (r := (H, x)).
  apply not_isprime_iff_iscomposite in r.
  destruct r as [d [[H1 H2] H3]].
  destruct (IHn d _ _) as [p r].
  exists p.
  exact _.
Defined.

(** Any natural number can either be written as a product of primes or is zero. *)
Definition prime_factorization@{} n
  : 0 < n
    -> exists (l : list Prime),
      n = fold_right (fun (p : Prime) n => nat_mul p n) 1 l.
Proof.
  revert n; snrapply nat_ind_strong; hnf; intros n IHn H.
  destruct H as [|n IH].
  1: exists nil; reflexivity.
  destruct (exists_prime_divisor n.+1 _) as [p d].
  pose proof (l := lt_divides d.1 n.+1 _ _ _).
  destruct d as [k H].
  destruct (IHn k l) as [f r].
  { destruct H, k.
    1: contradiction (lt_irrefl 0).
    exact _. }
  exists (p :: f)%list.
  simpl; destruct r.
  symmetry.
  lhs nrapply nat_mul_comm.
  exact H.
Defined.

(** TODO: show that any two prime factorizations are unique up to permutation of the lists. *)
