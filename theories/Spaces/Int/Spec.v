Require Import Basics.
Require Import Spaces.Pos.
Require Import Spaces.Int.Core.

Local Open Scope int_scope.

(** ** Addition is commutative *)

Lemma int_add_comm n m : n + m = m + n.
Proof.
  destruct n, m; cbn; trivial; by rewrite pos_add_comm.
Qed.

(** ** Zero is the additive identity. *)

Lemma int_add_0_l n : 0 + n = n.
Proof.
  reflexivity.
Qed.

Lemma int_add_0_r n : n + 0 = n.
Proof.
  by destruct n.
Qed.

(** ** Multiplication by zero is zero *)

Lemma int_mul_0_l n : 0 * n = 0.
Proof.
  reflexivity.
Qed.

Lemma int_mul_0_r n : n * 0 = 0.
Proof.
  by destruct n.
Qed.

(** ** One is the multiplicative identity *)

Lemma int_mul_1_l n : 1 * n = n.
Proof.
  by destruct n.
Qed.

Lemma int_mul_1_r n : n * 1 = n.
Proof.
  destruct n; trivial; cbn; apply ap, pos_mul_1_r.
Qed.

(** ** Inverse laws *)

Lemma int_pos_sub_diag n : int_pos_sub n n = 0.
Proof.
  induction n; trivial; cbn; by rewrite IHn.
Qed.

Lemma int_add_negation_l n : (-n) + n = 0.
Proof.
  destruct n; trivial; cbn; apply int_pos_sub_diag.
Qed.

Lemma int_add_negation_r n : n + (-n) = 0.
Proof.
  destruct n; trivial; cbn; apply int_pos_sub_diag.
Qed.

(** ** Permutation of neg and pos_succ *)
Lemma int_neg_pos_succ p : neg (pos_succ p) = int_pred (neg p).
Proof.
  by destruct p.
Qed.

(** ** Permutation of pos and pos_succ *)
Lemma int_pos_pos_succ p : pos (pos_succ p) = int_succ (pos p).
Proof.
  by destruct p.
Qed.

(** ** Negation of a doubled positive integer *)
Lemma int_negation_double a
  : - (int_double a) = int_double (- a).
Proof.
  by destruct a.
Qed.

(** Negation of the predecessor of a doubled positive integer. *)
Lemma int_negation_pred_double a
  : - (int_pred_double a) = int_succ_double (- a).
Proof.
  by destruct a.
Qed.

(** Negation of the doubling of the sucessor of an positive. *)
Lemma int_negation_succ_double a
  : - (int_succ_double a) = int_pred_double (- a).
Proof.
  by destruct a.
Qed.

(** Negation of subtraction of positive integers *)
Lemma int_pos_sub_negation a b
  : - (int_pos_sub a b) = int_pos_sub b a.
Proof.
  revert a b.
  induction a as [|a ah|a ah];
  destruct b;
  cbn; trivial.
  all: rewrite ?int_negation_double,
    ?int_negation_succ_double,
    ?int_negation_pred_double.
  all: apply ap, ah.
Qed.

(** ** int_succ is a retract of int_pred *)
Definition int_succ_pred : Sect int_pred int_succ.
Proof.
  intros [n | | n]; [|trivial|].
  all: destruct n; trivial.
  1,2: cbn; apply ap.
  1: apply pos_pred_double_succ.
  rewrite pos_add_1_r.
  apply pos_succ_pred_double.
Qed.

(** ** int_pred is a retract of int_succ *)
Definition int_pred_succ : Sect int_succ int_pred.
Proof.
  intros [n | | n]; [|trivial|].
  all: destruct n; trivial.
  1,2: cbn; apply ap.
  1: rewrite pos_add_1_r.
  1: apply pos_succ_pred_double.
  apply pos_pred_double_succ.
Qed.

(** ** Negation distributes over addition *)
Lemma int_negation_add_distr n m : - (n + m) = - n + - m.
Proof.
 destruct n, m; simpl; trivial using int_pos_sub_negation.
Qed.

(** ** Negation is injective *)
Lemma int_negation_inj n m : -n = -m -> n = m.
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
Qed.

(** ** Subtracting 1 from a sucessor gives the positive integer. *)
Lemma int_pos_sub_succ_l a
  : int_pos_sub (pos_succ a) 1%pos = pos a.
Proof.
  destruct a; trivial.
  cbn; apply ap, pos_pred_double_succ.
Qed.

(** ** Subtracting a sucessor from 1 gives minus the integer. *)
Lemma int_pos_sub_succ_r a
  : int_pos_sub 1%pos (pos_succ a) = neg a.
Proof.
  destruct a; trivial.
  cbn; apply ap, pos_pred_double_succ.
Qed.

(** ** Interaction of doubling functions and subtraction *)

Lemma int_succ_double_int_pos_sub a b
  : int_succ_double (int_pos_sub a (pos_succ b))
    = int_pred_double (int_pos_sub a b).
Proof.
  revert a b.
  induction a; induction b; trivial.
  + cbn; apply ap.
    by rewrite pos_pred_double_succ.
  + destruct a; trivial.
  + cbn; destruct (int_pos_sub a b); trivial.
  + cbn.
    rewrite <- IHa.
    destruct (int_pos_sub a (pos_succ b)); trivial.
  + destruct a; trivial.
  + cbn; destruct (int_pos_sub a b); trivial.
  + cbn.
    rewrite IHa.
    cbn; destruct (int_pos_sub a b); trivial.
Qed.

Lemma int_pred_double_int_pos_sub a b 
  : int_pred_double (int_pos_sub (pos_succ a) b)
    = int_succ_double (int_pos_sub a b).
Proof.
  revert a b.
  induction a; induction b; trivial.
  + by destruct b.
  + by destruct b.
  + cbn; by destruct (int_pos_sub a b).
  + cbn; by destruct (int_pos_sub a b).
  + cbn; apply ap.
    by rewrite pos_pred_double_succ.
  + cbn.
    rewrite <- IHa.
    by destruct (int_pos_sub (pos_succ a) b).
  + cbn.
    rewrite IHa.
    by destruct (int_pos_sub a b).
Qed.

(** ** Subtractions cancel sucessors. *)
Lemma int_pos_sub_succ_succ a b
  : int_pos_sub (pos_succ a) (pos_succ b) = int_pos_sub a b.
Proof.
  rewrite <- 2 pos_add_1_r.
  revert a b.
  induction a; induction b; trivial.
  1: destruct b; trivial.
  { destruct b; trivial.
    cbn; apply ap.
    by rewrite pos_pred_double_succ. }
  1: destruct a; trivial.
  1: apply int_succ_double_int_pos_sub.
  { destruct a; trivial.
    cbn; apply ap, ap, pos_pred_double_succ. }
  1: apply int_pred_double_int_pos_sub.
  cbn; apply ap.
  rewrite <- 2 pos_add_1_r.
  apply IHa.
Defined.

(** ** Predecessor of a subtraction is the subtraction of a sucessor. *)
Lemma int_pred_pos_sub_r a b
  : int_pred (int_pos_sub a b) = int_pos_sub a (pos_succ b).
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
  rewrite 2 int_pos_sub_succ_succ.
  apply bH.
Qed.

(** ** Negation of the predecessor is an involution. *)
Lemma int_negation_pred_negation_red x
  : - int_pred (- int_pred x) = x.
Proof.
  destruct x as [x| |x]; trivial;
  destruct x; trivial; cbn; apply ap.
  1: apply pos_pred_double_succ.
  rewrite pos_add_1_r.
  apply pos_succ_pred_double.
Qed.

(** ** Predecessor of a sum is the sum with a predecessor *)
Lemma int_pred_add_r a b
  : int_pred (a + b) = a + int_pred b.
Proof.
  revert a b.
  intros [a| |a] [b| |b]; trivial.
  + cbn; apply ap.
    by rewrite pos_add_assoc.
  + revert a.
    induction b as [|b bH] using pos_peano_ind.
    - intro a; exact (int_pred_succ (neg a)).
    - intro a.
      rewrite <- pos_add_1_r.
      rewrite (int_pred_succ (pos b)).
      rewrite int_add_comm.
      cbn.
      rewrite pos_add_1_r.
      rewrite <- int_pos_sub_negation.
      rewrite <- int_pred_pos_sub_r.
      apply int_negation_inj.
      rewrite int_pos_sub_negation.
      apply int_negation_pred_negation_red.
  + cbn.
    rewrite pos_add_1_r.
    apply int_pred_pos_sub_r.
  + revert a.
    induction b as [|b bH] using pos_peano_ind.
    - intro a; exact (int_pred_succ (pos a)).
    - intro a.
      rewrite <- pos_add_1_r.
      rewrite (int_pred_succ (pos b)).
      cbn; rewrite pos_add_assoc.
      change (int_pred (int_succ (pos (a + b)%pos)) = pos a + pos b).
      apply int_pred_succ.
Qed.

(** ** Subtraction from a sum is the sum of a subtraction *)
Lemma int_pos_sub_add (a b c : Pos)
  : int_pos_sub (a + b)%pos c = pos a + int_pos_sub b c.
Proof.
  revert c b a.
  induction c as [|c ch] using pos_peano_ind.
  { intros b a.
    change (int_pred (pos a + pos b) = pos a + (int_pred (pos b))).
    apply int_pred_add_r. }
  intros b a.
  rewrite <- int_pred_pos_sub_r.
  rewrite ch.
  rewrite <- int_pred_pos_sub_r.
  apply int_pred_add_r.
Qed.

(** An auxillary lemma used to prove associativity. *)
Lemma int_add_assoc_pos p n m : pos p + (n + m) = pos p + n + m.
Proof.
  destruct n as [n| |n], m as [m| |m]; trivial.
  - cbn; apply int_negation_inj.
    rewrite !int_negation_add_distr, !int_pos_sub_negation.
    rewrite int_add_comm, pos_add_comm.
    apply int_pos_sub_add.
  - symmetry.
    apply int_add_0_r.
  - by rewrite <- int_pos_sub_add, int_add_comm,
      <- int_pos_sub_add, pos_add_comm.
  - symmetry.
    apply int_pos_sub_add.
  - cbn; apply ap, pos_add_assoc.
Qed.

(** ** Associativity of addition *)
Lemma int_add_assoc n m p : n + (m + p) = n + m + p.
Proof.
  destruct n.
  - apply int_negation_inj.
    rewrite !int_negation_add_distr.
    apply int_add_assoc_pos.
  - trivial.
  - apply int_add_assoc_pos.
Qed.

(* ** The successor autoequivalence. *)
Global Instance isequiv_int_succ : IsEquiv int_succ | 0
  := isequiv_adjointify int_succ _ int_succ_pred int_pred_succ.

Definition equiv_int_succ : Int <~> Int
  := Build_Equiv _ _ _ isequiv_int_succ.

(** ** Commutativity of multplication *)
Lemma int_mul_comm n m : n * m = m * n.
Proof.
  destruct n, m; cbn; try reflexivity;
  apply ap; apply pos_mul_comm.
Qed.

(** Distributivity of multiplication over addition *)

Lemma int_pos_sub_mul_pos n m p
  : int_pos_sub n m * pos p = int_pos_sub (n * p)%pos (m * p)%pos.
Proof.
  rewrite int_mul_comm.
  rewrite 2 (pos_mul_comm _ p).
  induction p.
  { rewrite 2 pos_mul_1_l.
    apply int_mul_1_l. }
  { cbn.
    rewrite <- IHp.
    set (int_pos_sub n m) as k.
    by destruct k. }
  cbn.
  rewrite int_pos_sub_add.
  rewrite <- (int_pos_sub_negation _ (x0 _)).
  rewrite int_pos_sub_add.
  rewrite int_negation_add_distr.
  rewrite int_pos_sub_negation.
  rewrite int_add_assoc.
  cbn.
  rewrite <- IHp.
  set (int_pos_sub n m) as k.
  by destruct k.
Qed.

Lemma int_pos_sub_mul_neg n m p
  : int_pos_sub m n  * neg p = int_pos_sub (n * p)%pos (m * p)%pos.
Proof.
  rewrite int_mul_comm.
  rewrite 2 (pos_mul_comm _ p).
  induction p.
  { rewrite 2 pos_mul_1_l.
    rewrite <- int_pos_sub_negation.
    by destruct (int_pos_sub n m). }
  { cbn.
    rewrite <- IHp.
    rewrite <- int_pos_sub_negation.
    set (int_pos_sub n m) as k.
    by destruct k. }
  cbn.
  rewrite int_pos_sub_add.
  rewrite <- (int_pos_sub_negation _ (x0 _)).
  rewrite int_pos_sub_add.
  rewrite int_negation_add_distr.
  rewrite int_pos_sub_negation.
  rewrite int_add_assoc.
  cbn.
  rewrite <- IHp.
  rewrite <- (int_pos_sub_negation m).
  set (int_pos_sub m n) as k.
  by destruct k.
Qed.

Lemma int_mul_add_distr_r n m p : (n + m) * p = n * p + m * p.
Proof.
  induction p; destruct n, m; cbn; trivial; try f_ap;
  try apply pos_mul_add_distr_r;
  try apply int_pos_sub_mul_neg;
  try apply int_pos_sub_mul_pos;
  apply int_mul_0_r.
Qed.

Lemma int_mul_add_distr_l n m p : n * (m + p) = n * m + n * p.
Proof.
  rewrite 3 (int_mul_comm n); apply int_mul_add_distr_r.
Qed.

Lemma int_mul_assoc n m p : n * (m * p) = n * m * p.
Proof.
  destruct n, m, p; cbn; trivial; f_ap; apply pos_mul_assoc.
Qed.

