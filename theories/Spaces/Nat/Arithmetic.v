From HoTT Require Import Basics.
Require Import Spaces.Nat.Core.
  
Local Set Universe Minimization ToSet.

Local Close Scope trunc_scope.
Local Open Scope nat_scope.

(** TODO: The results in this file are in the process of being moved over to Core.v *)

(** TODO: move, rename *)
Proposition nataddsub_comm_ineq_lemma (n m : nat)
  : n.+1 - m <= (n - m).+1.
Proof.
  revert m.
  simple_induction n n IHn.
  - simple_induction m m IHm; exact _. 
  - intro m; simple_induction m m IHm.
    + apply leq_refl.
    + apply IHn.
Defined.

(** TODO: move, rename *)
Proposition nataddsub_comm_ineq (n m k : nat)
  : (n + k) - m <= (n - m) + k.
Proof.
  simple_induction k k IHk.
  - destruct (nat_add_zero_r n)^, (nat_add_zero_r (n - m))^; constructor.
  - destruct (nat_add_succ_r n k)^.
    refine (leq_trans (nataddsub_comm_ineq_lemma (n+k) m) _).
    destruct (nat_add_succ_r (n - m) k)^.
    by apply leq_succ.
Defined.

(** TODO: move, rename *)
Proposition nat_sub_add_ineq (n m : nat) : n <= n - m + m.
Proof.
  destruct (@leq_dichotomy m n) as [l | gt].
  - rewrite <- nat_sub_l_add_l; trivial.
    destruct (nat_add_sub_cancel_r n m)^.
    apply leq_refl; done.
  - apply leq_lt in gt.
    destruct (equiv_nat_sub_leq _)^.
    assumption.
Defined.

(** TODO: move, rename *)
Proposition i_lt_n_sum_m (n m i : nat)
  : i < n - m -> m <= n.
Proof.
  revert m i; simple_induction n n IHn.
  - intros m i l. simpl in l. contradiction (not_lt_zero_r _ _).
  - intros m i l. destruct m.
    + apply leq_zero_l.
    + apply leq_succ. simpl in l. exact (IHn m i l).
Defined.

(** TODO: move, rename *)
Proposition predeqminus1 { n : nat } : n - 1 = nat_pred n.
Proof.
  simple_induction' n.
  - reflexivity.
  - apply nat_sub_zero_r.
Defined.

(** TODO: move, rename *)
Proposition predn_leq_n (n : nat) : nat_pred n <= n.
Proof.
  destruct n; exact _.
Defined.

(** TODO: move, rename *)
Proposition pred_equiv (k n : nat) : k < n -> k < S (nat_pred n).
Proof. 
  intro ineq; destruct n.
  - contradiction (not_lt_zero_r _ _).
  - assumption.
Defined.

(** TODO: move, rename *)
Proposition n_leq_pred_Sn (n : nat) : n <= S (nat_pred n).
Proof. 
  destruct n; exact _.
Defined.

(** TODO: move, rename *)
Proposition leq_implies_pred_lt (i n k : nat)
  : (n > i) -> n <= k -> nat_pred n < k.
Proof.
  intro ineq; destruct n.
  - contradiction (not_lt_zero_r i).
  - intro; assumption.
Defined.
  
(** TODO: move, rename *)
Proposition pred_lt_implies_leq (n k : nat)
  : nat_pred n < k -> n <= k.
Proof.
  intro l; destruct n.
  - apply leq_zero_l.
  - assumption.
Defined.

(** TODO: move, rename *)
Proposition lt_implies_pred_geq (i j : nat) : i < j -> i <= nat_pred j.
Proof.
  intro l; apply leq_pred in l; assumption.
Defined.

(** TODO: move, rename *)
Proposition j_geq_0_lt_implies_pred_geq (i j k : nat)
  : i < j -> k.+1 <= j -> k <= nat_pred j.
Proof.
  intros l ineq.
  destruct j.
  - contradiction (not_lt_zero_r i).
  - by simpl; apply leq_pred'.
Defined.

(** TODO: move, rename *)
Proposition pred_gt_implies_lt (i j : nat)
  : i < nat_pred j -> i.+1 < j.
Proof.
  intros ineq.
  assert (H := leq_succ ineq). assert (i < j) as X. {
    apply (@lt_lt_leq_trans _ (nat_pred j) _);
      [assumption  | apply predn_leq_n].
  }
  by rewrite <- (nat_succ_pred' j i).
Defined.

(** TODO: move, rename *)
Proposition pred_preserves_lt {i n: nat} (p : i < n) m
  : (n < m) -> (nat_pred n < nat_pred m).
Proof.
  intro l.
  apply leq_pred'. destruct (symmetric_paths _ _ (nat_succ_pred' n i _)).
  set (k :=  transitive_lt i n m p l).
  destruct (symmetric_paths _ _ (nat_succ_pred' m i _)).
  assumption.
Defined.

(** TODO: move, rename *)
Proposition sub_less { n k : nat } : n - k <= n.
Proof.
  revert k.
  simple_induction n n IHn.
  - intros; apply leq_zero_l.
  - destruct k.
    + apply leq_refl.
    + simpl; apply (@leq_trans _ n _);
        [ apply IHn | apply leq_succ_r, leq_refl].
Defined.

(** TODO: move, rename *)
Proposition sub_less_strict { n k : nat }
  : 0 < n -> 0 < k -> n - k < n.
Proof.
  intros l l'.
  unfold "<".
  destruct k, n;
  try (contradiction (not_lt_zero_r _ _)).
  simpl; apply leq_succ, sub_less.
Defined.

(** TODO: move, rename *)
Proposition n_leq_m_n_leq_plus_m_k (n m k : nat)
  : n <= m -> n <= m + k.
Proof.
  intro l; apply (leq_trans l); exact (leq_add_r m k).
Defined.

(** This inductive type is defined because it lets you loop from [i = 0] up to [i = n] by structural induction on a proof of [increasing_geq n 0]. With the existing [leq] type and the inductive structure of [n], it is easier and more natural to loop downwards from [i = n] to [i = 0], but harder to find the least natural number in the interval $[0,n]$ satisfying a given property. *)

Local Unset Elimination Schemes.

Inductive increasing_geq (n : nat) : nat -> Type0 :=
| increasing_geq_n : increasing_geq n n
| increasing_geq_S (m : nat) : increasing_geq n m.+1 ->
                               increasing_geq n m.

Scheme increasing_geq_ind := Induction for increasing_geq Sort Type.
Scheme increasing_geq_rec := Minimality for increasing_geq Sort Type.
Definition increasing_geq_rect := increasing_geq_rec.

Local Set Elimination Schemes.

Proposition increasing_geq_S_n (n m : nat)
  : increasing_geq n m -> increasing_geq n.+1 m.+1.
Proof.
  intro a.
  induction a.
  - constructor.
  - by constructor.
Defined.

Proposition increasing_geq_n_0 (n : nat) : increasing_geq n 0.
Proof.
  simple_induction n n IHn.
  - constructor.
  - induction IHn.
    + constructor; by constructor.
    + constructor; by assumption.
Defined.

Lemma increasing_geq_minus (n k : nat)
  : increasing_geq n (n - k).
Proof.
  simple_induction k k IHk.
  - destruct (symmetric_paths _ _ (nat_sub_zero_r n)); constructor.
  - destruct (@leq_dichotomy n k) as [l | g].
    + destruct (equiv_nat_sub_leq _)^ in IHk.
      apply leq_succ_r in l.
      destruct (equiv_nat_sub_leq _)^. exact IHk.
    + change k.+1 with (1 + k). destruct (nat_add_comm k 1).
      destruct (symmetric_paths _ _ (nat_sub_r_add n k 1)).
      destruct (symmetric_paths _ _ (@predeqminus1 (n - k))).
      apply increasing_geq_S.
      unfold ">", "<" in *.
      apply equiv_lt_lt_sub in g. 
      by (destruct (symmetric_paths _ _ (nat_succ_pred (n - k) _))).
Defined.

Lemma ineq_sub' (n k : nat) : k < n -> n - k = (n - k.+1).+1.
Proof.
  intro ineq.
  destruct n.
  - contradiction (not_lt_zero_r k).
  - change (n.+1 - k.+1) with (n - k). apply leq_pred' in ineq.
    by apply nat_sub_succ_l.
Defined.
  
Lemma ineq_sub (n m : nat) : n <= m -> m - (m - n) = n.
Proof.
  revert m; simple_induction n n IHn.
  - intros. destruct (symmetric_paths _ _ (nat_sub_zero_r m)),
      (symmetric_paths _ _ (nat_sub_cancel m));
      reflexivity.
  - intros m ineq. change (m - n.+1) with (m - (1 + n)).
    (destruct (nat_add_comm n 1)).
    destruct (symmetric_paths _ _ (nat_sub_r_add m n 1)). 
    destruct (nat_succ_pred (m - n) (equiv_lt_lt_sub _ _ ineq)); simpl;
      destruct (symmetric_paths _ _ (nat_sub_zero_r (nat_pred (m - n)))).
    assert (0 < m - n) as dp by exact (equiv_lt_lt_sub _ _ ineq).
    assert (nat_pred (m - n) < m) as sh by
        ( unfold "<";
          destruct (symmetric_paths _ _ (nat_succ_pred _ _));
          exact sub_less).
    destruct (symmetric_paths _ _ (ineq_sub' _ _ _)).
    destruct (symmetric_paths _ _ (nat_succ_pred _ _)).
    apply (ap S), IHn, leq_succ_l, ineq.
Defined.                                 
  
Proposition leq_equivalent (n m : nat)
  : n <= m <-> increasing_geq m n.
Proof.
  split.
  - intro ineq. induction ineq.
    + constructor.
    + apply increasing_geq_S_n in IHineq; constructor; assumption.
  - intro a.
    induction a.
    + constructor.
    + exact (leq_succ_l _).
Defined.

(** TODO: remove *)
(** This tautology accepts a (potentially opaqued or QED'ed) proof of [n <= m], and returns a transparent proof which can be computed with (i.e., one can loop from n to m) *) 
Definition leq_wrapper {n m : nat} : n <= m -> n <= m.
Proof.
  intro ineq.
  destruct (@leq_dichotomy n m) as [l | g].
  - exact l.
  - contradiction (lt_irrefl m (lt_lt_leq_trans g ineq)).
Defined.

Proposition symmetric_rel_total_order (R : nat -> nat -> Type)
            {p : Symmetric R} {p' : Reflexive R}
  : (forall n m : nat, n < m -> R n m) -> (forall n m : nat, R n m).
Proof.
  intros A n m.
  destruct (@leq_dichotomy m n) as [m_leq_n | m_gt_n].
  - apply symmetry. destruct m_leq_n.
    + apply reflexivity.
    + apply A. apply leq_succ. assumption.
  - apply A, m_gt_n.
Defined.                             
