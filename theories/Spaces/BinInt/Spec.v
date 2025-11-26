From HoTT Require Import Basics.
Require Import Spaces.Pos.
Require Import Spaces.BinInt.Core.

Local Set Universe Minimization ToSet.

Local Open Scope binint_scope.

(** ** Addition is commutative *)

Lemma binint_add_comm n m : n + m = m + n.
Proof.
  destruct n, m; trivial. all: cbn.
  all: apply ap, pos_add_comm.
Defined.

(** ** Zero is the additive identity. *)

Definition binint_add_0_l n : 0 + n = n
  := 1.

Lemma binint_add_0_r n : n + 0 = n.
Proof.
  by destruct n.
Defined.

(** ** Multiplication by zero is zero *)

Definition binint_mul_0_l n : 0 * n = 0
  := 1.

Lemma binint_mul_0_r n : n * 0 = 0.
Proof.
  by destruct n.
Defined.

(** ** One is the multiplicative identity *)

Lemma binint_mul_1_l n : 1 * n = n.
Proof.
  by destruct n.
Defined.

Lemma binint_mul_1_r n : n * 1 = n.
Proof.
  destruct n; trivial; cbn; apply ap, pos_mul_1_r.
Defined.

(** ** Inverse laws *)

Lemma binint_pos_sub_diag n : binint_pos_sub n n = 0.
Proof.
  induction n; trivial; cbn.
  all: exact (ap binint_double IHn).
Defined.

Lemma binint_add_negation_l n : (-n) + n = 0.
Proof.
  destruct n; trivial; cbn; apply binint_pos_sub_diag.
Defined.

Lemma binint_add_negation_r n : n + (-n) = 0.
Proof.
  destruct n; trivial; cbn; apply binint_pos_sub_diag.
Defined.

(** ** Permutation of [neg] and [pos_succ] *)
Lemma binint_neg_pos_succ p : neg (pos_succ p) = binint_pred (neg p).
Proof.
  by destruct p.
Defined.

(** ** Permutation of [pos] and [pos_succ] *)
Lemma binint_pos_pos_succ p : pos (pos_succ p) = binint_succ (pos p).
Proof.
  by destruct p.
Defined.

(** ** Negation of a doubled positive integer *)
Lemma binint_negation_double a : - (binint_double a) = binint_double (- a).
Proof.
  by destruct a.
Defined.

(** Negation of the predecessor of a doubled positive integer. *)
Lemma binint_negation_pred_double a
  : - (binint_pred_double a) = binint_succ_double (- a).
Proof.
  by destruct a.
Defined.

(** Negation of the doubling of the successor of an positive. *)
Lemma binint_negation_succ_double a
  : - (binint_succ_double a) = binint_pred_double (- a).
Proof.
  by destruct a.
Defined.

(** Negation of subtraction of positive integers *)
Lemma binint_pos_sub_negation a b
  : - (binint_pos_sub a b) = binint_pos_sub b a.
Proof.
  revert a b.
  induction a as [|a ah|a ah];
  destruct b;
  cbn; trivial.
  all: rewrite ?binint_negation_double,
    ?binint_negation_succ_double,
    ?binint_negation_pred_double.
  all: apply ap, ah.
Defined.

(** ** [binint_succ] is a retract of [binint_pred] *)
Definition binint_succ_pred : binint_succ o binint_pred == idmap.
Proof.
  intros [n | | n]; [|trivial|].
  all: destruct n; trivial.
  1,2: cbn; apply ap.
  1: apply pos_pred_double_succ.
  rewrite pos_add_1_r.
  apply pos_succ_pred_double.
Defined.

(** ** [binint_pred] is a retract of [binint_succ] *)
Definition binint_pred_succ : binint_pred o binint_succ == idmap.
Proof.
  intros [n | | n]; [|trivial|].
  all: destruct n; trivial.
  1,2: cbn; apply ap.
  1: rewrite pos_add_1_r.
  1: apply pos_succ_pred_double.
  apply pos_pred_double_succ.
Defined.

(* ** The successor auto-equivalence. *)
Instance isequiv_binint_succ : IsEquiv binint_succ | 0
  := isequiv_adjointify binint_succ _ binint_succ_pred binint_pred_succ.

Definition equiv_binint_succ : BinInt <~> BinInt
  := Build_Equiv _ _ _ isequiv_binint_succ.

(** ** Negation distributes over addition *)
Lemma binint_negation_add_distr n m : - (n + m) = - n + - m.
Proof.
 destruct n, m; simpl; trivial using binint_pos_sub_negation.
Defined.

(** ** Negation is injective *)
Lemma binint_negation_inj n m : -n = -m -> n = m.
Proof.
  destruct n, m; simpl; intro H.
  1: apply pos_inj in H.
  2: apply pos_neq_zero in H.
  3: apply pos_neq_neg in H.
  4: apply  zero_neq_pos in H.
  6: apply  zero_neq_neg in H.
  7: apply  neg_neq_pos in H.
  8: apply  neg_neq_zero in H.
  9: apply  neg_inj in H.
  all: by destruct H.
Defined.

(** ** Subtracting 1 from a successor gives the positive integer. *)
Lemma binint_pos_sub_succ_l a
  : binint_pos_sub (pos_succ a) 1%pos = pos a.
Proof.
  destruct a; trivial.
  cbn; apply ap, pos_pred_double_succ.
Defined.

(** ** Subtracting a successor from 1 gives minus the integer. *)
Lemma binint_pos_sub_succ_r a
  : binint_pos_sub 1%pos (pos_succ a) = neg a.
Proof.
  destruct a; trivial.
  cbn; apply ap, pos_pred_double_succ.
Defined.

(** ** Interaction of doubling functions and subtraction *)

Lemma binint_succ_double_binint_pos_sub a b
  : binint_succ_double (binint_pos_sub a (pos_succ b))
    = binint_pred_double (binint_pos_sub a b).
Proof.
  revert a b.
  induction a; induction b; trivial.
  + cbn; apply ap.
    by rewrite pos_pred_double_succ.
  + destruct a; trivial.
  + cbn; destruct (binint_pos_sub a b); trivial.
  + cbn.
    rewrite <- IHa.
    destruct (binint_pos_sub a (pos_succ b)); trivial.
  + destruct a; trivial.
  + cbn; destruct (binint_pos_sub a b); trivial.
  + cbn.
    rewrite IHa.
    cbn; destruct (binint_pos_sub a b); trivial.
Defined.

Lemma binint_pred_double_binint_pos_sub a b 
  : binint_pred_double (binint_pos_sub (pos_succ a) b)
    = binint_succ_double (binint_pos_sub a b).
Proof.
  revert a b.
  induction a; induction b; trivial.
  + by destruct b.
  + by destruct b.
  + cbn; by destruct (binint_pos_sub a b).
  + cbn; by destruct (binint_pos_sub a b).
  + cbn; apply ap.
    by rewrite pos_pred_double_succ.
  + cbn.
    rewrite <- IHa.
    by destruct (binint_pos_sub (pos_succ a) b).
  + cbn.
    rewrite IHa.
    by destruct (binint_pos_sub a b).
Defined.

(** ** Subtractions cancel successors. *)
Lemma binint_pos_sub_succ_succ a b
  : binint_pos_sub (pos_succ a) (pos_succ b) = binint_pos_sub a b.
Proof.
  rewrite <- 2 pos_add_1_r.
  revert a b.
  induction a; induction b; trivial.
  1: destruct b; trivial.
  { destruct b; trivial.
    cbn; apply ap.
    by rewrite pos_pred_double_succ. }
  1: destruct a; trivial.
  1: apply binint_succ_double_binint_pos_sub.
  { destruct a; trivial.
    cbn; apply ap, ap, pos_pred_double_succ. }
  1: apply binint_pred_double_binint_pos_sub.
  cbn; apply ap.
  rewrite <- 2 pos_add_1_r.
  apply IHa.
Defined.

(** ** Predecessor of a subtraction is the subtraction of a successor. *)
Lemma binint_pred_pos_sub_r a b
  : binint_pred (binint_pos_sub a b) = binint_pos_sub a (pos_succ b).
Proof.
  revert a.
  induction b as [|b bH] using pos_peano_ind.
  1: destruct a; trivial; destruct a; trivial.
  intro a.
  revert b bH.
  induction a as [|a aH] using pos_peano_ind.
  { intros b bH.
    rewrite <- bH.
    destruct b; trivial.
    cbn; apply ap.
    rewrite 2 pos_add_1_r.
    rewrite pos_succ_pred_double.
    rewrite pos_pred_double_succ.
    trivial. }
  intros b bH.
  rewrite 2 binint_pos_sub_succ_succ.
  apply bH.
Defined.

(** ** Negation of the predecessor is an involution. *)
Lemma binint_negation_pred_negation_red x
  : - binint_pred (- binint_pred x) = x.
Proof.
  destruct x as [x| |x]; trivial;
  destruct x; trivial; cbn; apply ap.
  1: apply pos_pred_double_succ.
  rewrite pos_add_1_r.
  apply pos_succ_pred_double.
Defined.

(** ** Predecessor of a sum is the sum with a predecessor *)
Lemma binint_pred_add_r a b
  : binint_pred (a + b) = a + binint_pred b.
Proof.
  revert a b.
  intros [a| |a] [b| |b]; trivial.
  + cbn; apply ap.
    by rewrite pos_add_assoc.
  + revert a.
    induction b as [|b bH] using pos_peano_ind.
    - intro a; exact (binint_pred_succ (neg a)).
    - intro a.
      rewrite <- pos_add_1_r.
      rewrite (binint_pred_succ (pos b)).
      rewrite binint_add_comm.
      cbn.
      rewrite pos_add_1_r.
      rewrite <- binint_pos_sub_negation.
      rewrite <- binint_pred_pos_sub_r.
      apply binint_negation_inj.
      rewrite binint_pos_sub_negation.
      apply binint_negation_pred_negation_red.
  + cbn.
    rewrite pos_add_1_r.
    apply binint_pred_pos_sub_r.
  + revert a.
    induction b as [|b bH] using pos_peano_ind.
    - intro a; exact (binint_pred_succ (pos a)).
    - intro a.
      rewrite <- pos_add_1_r.
      rewrite (binint_pred_succ (pos b)).
      cbn; rewrite pos_add_assoc.
      change (binint_pred (binint_succ (pos (a + b)%pos)) = pos a + pos b).
      apply binint_pred_succ.
Defined.

(** ** Subtraction from a sum is the sum of a subtraction *)
Lemma binint_pos_sub_add (a b c : Pos)
  : binint_pos_sub (a + b)%pos c = pos a + binint_pos_sub b c.
Proof.
  revert c b a.
  induction c as [|c ch] using pos_peano_ind.
  { intros b a.
    change (binint_pred (pos a + pos b) = pos a + (binint_pred (pos b))).
    apply binint_pred_add_r. }
  intros b a.
  rewrite <- binint_pred_pos_sub_r.
  rewrite ch.
  rewrite <- binint_pred_pos_sub_r.
  apply binint_pred_add_r.
Defined.

(** An auxiliary lemma used to prove associativity. *)
Lemma binint_add_assoc_pos p n m : pos p + (n + m) = pos p + n + m.
Proof.
  destruct n as [n| |n], m as [m| |m]; trivial.
  - cbn; apply binint_negation_inj.
    rewrite !binint_negation_add_distr, !binint_pos_sub_negation.
    rewrite binint_add_comm, pos_add_comm.
    apply binint_pos_sub_add.
  - symmetry.
    apply binint_add_0_r.
  - by rewrite <- binint_pos_sub_add, binint_add_comm,
      <- binint_pos_sub_add, pos_add_comm.
  - symmetry.
    apply binint_pos_sub_add.
  - cbn; apply ap, pos_add_assoc.
Defined.

(** ** Associativity of addition *)
Lemma binint_add_assoc n m p : n + (m + p) = n + m + p.
Proof.
  destruct n.
  - apply binint_negation_inj.
    rewrite !binint_negation_add_distr.
    apply binint_add_assoc_pos.
  - trivial.
  - apply binint_add_assoc_pos.
Defined.

(** ** Relationship between [int_succ], [int_pred] and addition. *)
Lemma binint_add_succ_l a b : binint_succ a + b = binint_succ (a + b).
Proof.
  rewrite <- binint_add_assoc, (binint_add_comm 1 b).
  apply binint_add_assoc.
Defined.

Lemma binint_add_succ_r a b : a + binint_succ b = binint_succ (a + b).
Proof.
  apply binint_add_assoc.
Defined.

Lemma binint_add_pred_l a b : binint_pred a + b = binint_pred (a + b).
Proof.
  rewrite <- binint_add_assoc, (binint_add_comm (-1) b).
  apply binint_add_assoc.
Defined.

Lemma binint_add_pred_r a b : a + binint_pred b = binint_pred (a + b).
Proof.
  apply binint_add_assoc.
Defined.

(** ** Commutativity of multiplication *)
Lemma binint_mul_comm n m : n * m = m * n.
Proof.
  destruct n, m; cbn; try reflexivity;
  apply ap; apply pos_mul_comm.
Defined.

(** Distributivity of multiplication over addition *)

Lemma binint_pos_sub_mul_pos n m p
  : binint_pos_sub n m * pos p = binint_pos_sub (n * p)%pos (m * p)%pos.
Proof.
  rewrite binint_mul_comm.
  rewrite 2 (pos_mul_comm _ p).
  induction p.
  { rewrite 2 pos_mul_1_l.
    apply binint_mul_1_l. }
  { cbn.
    rewrite <- IHp.
    set (binint_pos_sub n m) as k.
    by destruct k. }
  cbn.
  rewrite binint_pos_sub_add.
  rewrite <- (binint_pos_sub_negation _ (x0 _)).
  rewrite binint_pos_sub_add.
  rewrite binint_negation_add_distr.
  rewrite binint_pos_sub_negation.
  rewrite binint_add_assoc.
  cbn.
  rewrite <- IHp.
  set (binint_pos_sub n m) as k.
  by destruct k.
Defined.

Lemma binint_pos_sub_mul_neg n m p
  : binint_pos_sub m n  * neg p = binint_pos_sub (n * p)%pos (m * p)%pos.
Proof.
  rewrite binint_mul_comm.
  rewrite 2 (pos_mul_comm _ p).
  induction p.
  { rewrite 2 pos_mul_1_l.
    rewrite <- binint_pos_sub_negation.
    by destruct (binint_pos_sub n m). }
  { cbn.
    rewrite <- IHp.
    rewrite <- binint_pos_sub_negation.
    set (binint_pos_sub n m) as k.
    by destruct k. }
  cbn.
  rewrite binint_pos_sub_add.
  rewrite <- (binint_pos_sub_negation _ (x0 _)).
  rewrite binint_pos_sub_add.
  rewrite binint_negation_add_distr.
  rewrite binint_pos_sub_negation.
  rewrite binint_add_assoc.
  cbn.
  rewrite <- IHp.
  rewrite <- (binint_pos_sub_negation m).
  set (binint_pos_sub m n) as k.
  by destruct k.
Defined.

Lemma binint_mul_add_distr_r n m p : (n + m) * p = n * p + m * p.
Proof.
  induction p; destruct n, m; cbn; trivial; try f_ap;
  try apply pos_mul_add_distr_r;
  try apply binint_pos_sub_mul_neg;
  try apply binint_pos_sub_mul_pos;
  apply binint_mul_0_r.
Defined.

Lemma binint_mul_add_distr_l n m p : n * (m + p) = n * m + n * p.
Proof.
  rewrite 3 (binint_mul_comm n); apply binint_mul_add_distr_r.
Defined.

Lemma binint_mul_assoc n m p : n * (m * p) = n * m * p.
Proof.
  destruct n, m, p; cbn; trivial; f_ap; apply pos_mul_assoc.
Defined.
