Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable Basics.Equivalences.
Require Basics.Numerals.Decimal.
Require Import Spaces.Nat.Core Spaces.Nat.Arithmetic.

Unset Elimination Schemes.
Set Universe Minimization ToSet.
Set Cumulativity Weak Constraints.

Declare Scope int_scope.

(** * The Integers *)

(** ** Definition *)

(** We define the integers as two copies of [nat] stuck together. This allows us to reuse many lemmas about arithmetic in nat to prove similar lemmas about integers. *)

Inductive Int : Type0 :=
| pos :> nat -> Int
| negS : nat -> Int.

(** ** Number Notations *)

(** Printing *)
Definition int_to_number_int (n : Int) : Numeral.int :=
  match n with
  | pos n => Numeral.IntDec (Decimal.Pos (Nat.to_uint n))
  | negS n => Numeral.IntDec (Decimal.Neg (Nat.to_uint (S n)))
  end.

(** Parsing *)
Definition int_of_number_int (d : Numeral.int) :=
  match d with
  | Numeral.IntDec (Decimal.Pos d) => pos (Nat.of_uint d)
  | Numeral.IntDec (Decimal.Neg d) => negS (pred (Nat.of_uint d))
  | Numeral.IntHex (Hexadecimal.Pos u) => pos (Nat.of_hex_uint u)
  | Numeral.IntHex (Hexadecimal.Neg u) => negS (pred (Nat.of_hex_uint u))
  end.

Number Notation Int int_of_number_int int_to_number_int : int_scope.

Delimit Scope int_scope with int.
Local Open Scope int_scope.

(** ** Basic Properties *)

(** The integers have decidable equality. *)
Global Instance decidable_paths_int@{} : DecidablePaths Int.
Proof.
  intros x y.
  destruct x as [x | x], y as [y | y].
  2,3: right; intros; discriminate.
  1,2: nrapply decidable_iff.
  1,4: nrapply ap.
  1,3: intros H; by injection H.
  1,2: exact _.
Defined.

(** By Hedberg's theorem, we have that the integers are a set. *)
Global Instance ishset_int@{} : IsHSet Int := _.

(** ** Operations *)

(** *** Negation *)

(** We define negation of integers by cases on the signs of the integers. *)
Definition int_neg@{} (x : Int) : Int :=
  match x with
  | pos 0 => pos 0
  | pos x.+1 => negS x
  | negS x => pos x.+1
  end.

Notation "- x" := (int_neg x) : int_scope.

(** *** Addition *)

(** We define addition of integers by cases on the signs of the integers. *)
Definition int_add@{} (x y : Int) : Int :=
  match x, y with
  | pos x, pos y => pos (x + y)
  | negS x, negS y => negS (x + y).+1
  | negS x, pos y
  | pos y, negS x => if (dec (x < y))%nat then pos (y - x.+1) else negS (x - y)
  end.

Infix "+" := int_add : int_scope.
Infix "-" := (fun x y => x + -y) : int_scope.

(** *** Multiplication *)

(** We define multiplication of integers by cases on the signs of the integers. Note that in the [negS y, pos x] case the order of the multplication is swapped. This is a trick so that the proof of commutativity becomes easier. *)
Definition int_mul@{} (x y : Int) : Int :=
  match x, y with
  | pos x, pos y => pos (x * y)
  | negS x, negS y => pos (x.+1 * y.+1)
  | pos x, negS y => - pos (x * y.+1)
  | negS y, pos x => - pos (x * y.+1)
  end.

Infix "*" := int_mul : int_scope.

(** *** Integer induction *)

(** The induction principle for integers is similar to the induction principle for natural numbers. However we have two induction hypotheses going in either direction starting from 0. *)
Definition Int_ind@{i} (P : Int -> Type@{i})
  (H0 : P (pos 0))
  (HP : forall n : nat, P n -> P n.+1%nat)
  (HN : forall n : nat, P (- n) -> P (- n.+1%nat))
  : forall x, P x.
Proof.
  intros [x | x].
  - induction x as [|x IHx].
    + apply H0.
    + apply HP, IHx.
  - induction x as [|x IHx].
    + apply HN, H0.
    + apply HN, IHx.
Defined.

(** We record these so that they can be used with the [induction] tactic. *)
Definition Int_rect := Int_ind.
Definition Int_rec := Int_ind.

(** ** Properties of Operations *)

(** *** Negation *)

(** Negation is involutive. *)
Definition int_neg_neg@{} (x : Int) : - - x = x.  
Proof.
  by induction x; simpl.
Defined.

(** Negation is an equivalence. *)
Global Instance isequiv_int_neg@{} : IsEquiv int_neg.
Proof.
  snrapply (isequiv_adjointify int_neg int_neg).
  1,2: nrapply int_neg_neg.
Defined.

(** Negation is injective. *)
Definition isinj_int_neg@{} (x y : Int) : int_neg x = int_neg y -> x = y.
Proof.
  apply (equiv_inj int_neg).
Defined.

(** TODO: eauto helped prove goals here. Work out a way to make this proof even easier. *)
(** Negation distributes over addition. *)
Definition int_neg_add@{} (x y : Int) : - (x + y) = - x - y.
Proof.
  destruct x as [[|x] | x], y as [[|y] | y]; trivial; simpl.
  1-3,6: rewrite sub_n_0; trivial.
  1,2: by rewrite <- add_n_O.
  1,4: by rewrite add_n_Sm.
  1,2: change (negS ?x) with (- x.+1)%nat.
  1,2: destruct (dec (y <= x)%nat) as [H | H], (dec (x <= y)%nat) as [H' | H'].
  - assert (H'' : x = y).
    1: apply leq_antisym; trivial.
    destruct H''.
    decidable_true (dec (x < x.+1)%nat) (n_lt_Sn x).
    by rewrite sub_n_n.
  - apply not_leq_implies_gt in H'.
    assert (H'' : (y < x.+1)%nat) by rapply lt_trans.
    decidable_true (dec (y < x.+1)%nat) H''.
    apply lt_implies_not_geq in H''.
    assert (H''' : ~(x < y.+1)%nat) by eauto with nat.
    decidable_false (dec (x < y.+1)%nat) H'''.
    rewrite ineq_sub'; trivial.
  - apply not_leq_implies_gt in H.
    assert (H'' : ~ (y < x.+1)%nat) by eauto with nat.
    decidable_false (dec (y < x.+1)%nat) H''.
    assert (H''' : (x < y.+1)%nat) by eauto with nat.
    decidable_true (dec (x < y.+1)%nat) H'''.
    rewrite <- ineq_sub'; trivial.
    apply int_neg_neg.
  - contradiction H.
    eauto with nat.
  - assert (H'' : x = y).
    1: apply leq_antisym; trivial.
    destruct H''.
    decidable_true (dec (x < x.+1)%nat) (n_lt_Sn x).
    by rewrite sub_n_n.
  - apply not_leq_implies_gt in H'.
    assert (H'' : (y < x.+1)%nat) by rapply lt_trans.
    decidable_true (dec (y < x.+1)%nat) H''.
    apply lt_implies_not_geq in H''.
    assert (H''' : ~(x < y.+1)%nat) by eauto with nat.
    decidable_false (dec (x < y.+1)%nat) H'''.
    rewrite <- ineq_sub'; trivial.
    apply int_neg_neg.
  - apply not_leq_implies_gt in H.
    assert (H'' : ~ (y < x.+1)%nat) by eauto with nat.
    decidable_false (dec (y < x.+1)%nat) H''.
    assert (H''' : (x < y.+1)%nat) by eauto with nat.
    decidable_true (dec (x < y.+1)%nat) H'''.
    rewrite <- ineq_sub'; trivial.
  - contradiction H.
    eauto with nat.
Defined.

(** *** Addition *)

(** Integer addition is commutative. *)
Definition int_add_comm@{} (x y : Int) : x + y = y + x.
Proof.
  destruct x as [x | x], y as [y | y]; trivial; simpl.
  1,2: by rewrite nat_add_comm.
Defined.

(** Integer addition with zero on the left is the identity. *)
Definition int_add_0_l@{} (x : Int) : 0 + x = x.
Proof.
  by destruct x as [[] | []].
Defined.

(** Integer addition with zero on the right is the identity. *)
Definition int_add_0_r@{} (x : Int) : x + 0 = x.
Proof.
  by rewrite int_add_comm, int_add_0_l.
Defined. 

(** TODO: cleanup *)
(** Adding a successor of a nat on the left is the successor of the sum. *) 
Definition int_add_S_nat_l@{} (n : nat) (y : Int) : n.+1%nat + y = 1 + (n + y).
Proof.
  destruct y as [|m].
  - reflexivity.
  - simpl.
    destruct (dec (m < n)%nat) as [H | H].
    + decidable_true (dec (m < n.+1)%nat) (lt_trans H _).
      induction n as [|n IHn] in m, H |- * using nat_rect@{Set}.
      1: by apply not_lt_n_0 in H.
      destruct m.
      1: simpl; by rewrite sub_n_0.
      by apply IHn, leq_S_n.
    + apply not_lt_implies_geq in H.
      destruct (dec (m < n.+1))%nat as [H' | H'].
      * apply leq_S_n in H'.
        destruct (leq_antisym H H').
        by rewrite sub_n_n.
      * apply not_lt_implies_geq in H'.
        destruct (dec (m - n < 1)%nat) as [H'' | H''].
        { assert (H''' : m = n).
          { apply natpmswap4 in H''.
            rewrite <- add_n_Sm in H''.
            rewrite <- add_n_O in H''.
            eauto with nat. }
          destruct H'''.
          eauto with nat. }
        apply ap.
        rewrite <- subsubadd.
        f_ap.
        by rewrite <- add_n_Sm, <- add_n_O.
Defined.

(** Adding a successor of a nat on the right is the successor of the sum. *)
Definition int_add_S_nat_r@{} (x : Int) (n : nat) : x + n.+1%nat = 1 + (x + n).
Proof.
  by rewrite int_add_comm, int_add_S_nat_l, (int_add_comm x).
Defined.

(** The sucessor of a predecessor is the identity. *)
Definition int_add_S_pred@{} (x : Int) : 1 + (x - 1) = x.
Proof.
  destruct x as [x | x].
  - destruct x; trivial.
    simpl.
    assert (H : (0 < x.+1)%nat) by eauto with nat.
    decidable_true (dec (0 < x.+1)%nat) H.
    by rewrite sub_n_0.
  - simpl.
    by rewrite sub_n_0, <- add_n_O.
Defined.

(** The predessor of a sucessor is the identity. *)
Definition int_add_pred_S@{} (x : Int) : (1 + x) - 1 = x.
Proof.
  apply isinj_int_neg.
  rewrite 2 int_neg_add.
  rewrite int_neg_neg.
  rewrite int_add_comm.
  rewrite (int_add_comm (-1)).
  apply int_add_S_pred.
Defined.

(** Adding a successor on the left is the sucessor of the sum. *)
Definition int_add_S_l@{} (x y : Int) : (1 + x) + y = 1 + (x + y).
Proof.
  destruct x as [x | x].
  - change (x.+1%nat + y = 1 + (x + y)).
    by rewrite int_add_S_nat_l.
  - apply isinj_int_neg.
    rewrite 4 int_neg_add.
    change (negS x) with (- x.+1)%nat.
    rewrite int_neg_neg.
    rewrite (int_add_S_nat_l _ (-y)).
    rewrite (int_add_comm (-1)).
    rewrite (int_add_S_nat_l ).
    rewrite (int_add_comm (-1)).
    rewrite int_add_S_pred.
    by rewrite int_add_pred_S.
Defined.

(** Adding a successor on the right is the sucessor of the sum. *)
Definition int_add_S_r@{} (x y : Int) : x + (1 + y) = 1 + (x + y).
Proof.
  by rewrite int_add_comm, int_add_S_l, (int_add_comm x).
Defined.

(** Adding a predecessor on the left is the predecessor of the sum. *)
Definition int_add_sub1@{} (x y : Int) : (x - 1) + y = (x + y) - 1.
Proof.
  rewrite <- (int_neg_neg x), <- (int_neg_neg y).
  generalize (-x) (-y); clear x y; intros x y.
  rewrite <- !int_neg_add.
  rewrite 2 (int_add_comm _ 1).
  by rewrite int_add_S_l.
Defined.

(** Integer addition is associative. *)
Definition int_add_assoc@{} (x y z : Int) : x + (y + z) = x + y + z.
Proof.
  induction x as [|x IHx|x IHx] in y, z |- *.
  - by rewrite 2 int_add_0_l.
  - change (x.+1)%nat with (1 + x)%nat.
    change (pos (?n + ?m)%nat) with (n + m)%int.
    rewrite !(int_add_S_l x), int_add_S_l. 
    by rewrite IHx.
  - change (x.+1)%nat with (1 + x)%nat.
    rewrite nat_add_comm.
    change (pos (?n + ?m)%nat) with (n + m)%int.
    rewrite (int_neg_add x 1).
    rewrite !int_add_sub1.
    by rewrite IHx.
Defined.

(** Integer addition has left inverses. *)
Definition int_add_neg_l@{} (x : Int) : - x + x = 0.
Proof.
  induction x; trivial.
  1,2: simpl; rewrite sub_n_n.
  1,2: by decidable_true (dec (n < n.+1)%nat) (n_lt_Sn n).
Defined.

(** Integer addition has right inverses. *)
Definition int_add_neg_r@{} (x : Int) : x - x = 0.
Proof.
  unfold "-"; by rewrite int_add_comm, int_add_neg_l.
Defined.

(** *** Multiplication *)

(** Integer multiplication is commutative. *)
Definition int_mul_comm@{} (x y : Int) : x * y = y * x.
Proof.
  destruct x as [x | x], y as [y | y]; trivial; unfold "*";
    by rewrite nat_mul_comm.
Defined.

(** Integer multiplication with one on the left is the identity. *)
Definition int_mul_1_l@{} (x : Int) : 1 * x = x.
Proof.
  destruct x as [x | x]; trivial; simpl;
    by rewrite <- add_n_O.
Defined.

(** Integer multiplication with one on the right is the identity. *)
Definition int_mul_1_r@{} (x : Int) : x * 1 = x. 
Proof.
  by rewrite int_mul_comm, int_mul_1_l.
Defined.

(** Integer multiplication with zero on the left is zero. *)
Definition int_mul_0_l@{} (x : Int) : 0 * x = 0.
Proof.
  by destruct x as [[] | []].
Defined.

(** Integer multiplication with zero on the right is zero. *)
Definition int_mul_0_r@{} (x : Int) : x * 0 = 0.
Proof.
  by rewrite int_mul_comm, int_mul_0_l.
Defined.

(** Multiplying with a negation on the left is the same as negating the product. *)
Definition int_mul_neg_l@{} (x y : Int) : - x * y = - (x * y).
Proof.
  destruct x as [x | x], y as [y | y]; trivial.
  - rewrite int_mul_comm.
    destruct x.
    1: by rewrite !int_mul_0_r.
    apply (ap int_neg).
    by rewrite int_mul_comm.
  - rewrite int_neg_neg.
    by destruct x.
  - by rewrite int_neg_neg, int_mul_comm.
Defined.

(** Multiplying with a negation on the right is the same as negating the product. *)
Definition int_mul_neg_r@{} (x y : Int) : x * - y = - (x * y).
Proof.
  rewrite !(int_mul_comm x).
  apply int_mul_neg_l.
Defined.

(** Multipication with a sucessor on the left can be unfolded. *)
Definition int_mul_S_nat_l@{} (n : nat) (y : Int) : n.+1%nat * y = y + n * y.
Proof.
  destruct y as [m | m].
  - reflexivity.
  - change ((n.+1)%nat * - (m.+1)%nat = - (m.+1)%nat + n * -(m.+1)%nat).
    by rewrite 2 int_mul_neg_r, <- int_neg_add.
Defined.

(** Multipication with a sucessor on the right can be unfolded. *)
Definition int_mul_S_nat_r@{} (x : Int) (n : nat) : x * n.+1%nat = x + x * n.
Proof.
  by rewrite int_mul_comm, int_mul_S_nat_l, (int_mul_comm x).
Defined.

(** Multiplication distributes over addition on the left. *)
Definition int_dist_l@{} (x y z : Int) : x * (y + z) = x * y + x * z.
Proof.
  induction x as [|x IHx|x IHx] in y, z |- *.
  - by rewrite 3 int_mul_0_l.
  - change ((x.+1)%nat * (y + z) = (x.+1)%nat * y + (x.+1)%nat * z).
    rewrite 3 int_mul_S_nat_l.
    rewrite IHx.
    rewrite !int_add_assoc.
    rewrite 2 (int_add_comm _ (x * y)).
    by rewrite int_add_assoc.
  - rewrite 3 int_mul_neg_l.
    rewrite 3 int_mul_S_nat_l.
    rewrite int_neg_add.
    rewrite <- int_mul_neg_l.
    rewrite IHx.
    rewrite !int_neg_add.
    rewrite !int_add_assoc.
    rewrite <- 2 int_mul_neg_l.
    f_ap.
    rewrite <- 2 int_add_assoc.
    f_ap.
    by rewrite int_add_comm.
Defined.

(** Multiplication distributes over addition on the right. *)
Definition int_dist_r@{} (x y z : Int) : (x + y) * z = x * z + y * z.
Proof.
  by rewrite int_mul_comm, int_dist_l, !(int_mul_comm z).
Defined.

(** Multiplication is associative. *)
Definition int_mul_assoc@{} (x y z : Int) : x * (y * z) = x * y * z.
Proof.
  induction x as [|x IHx|x IHx] in y, z |- *.
  - by rewrite 3 int_mul_0_l.
  - rewrite 2 int_mul_S_nat_l.
    rewrite int_dist_r.
    f_ap.
  - rewrite 3 int_mul_neg_l.
    rewrite 2 int_mul_S_nat_l.
    rewrite int_dist_r.
    rewrite 2 int_neg_add.
    f_ap.
    rewrite <- 3 int_mul_neg_l.
    apply IHx.
Defined.
