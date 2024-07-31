Require Import Basics.
Require Import Spaces.Nat.Core.
  
Local Set Universe Minimization ToSet.

Local Close Scope trunc_scope.
Local Open Scope nat_scope.

(** TODO: The results in this file are in the process of being moved over to Core.v *)

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

Proposition nataddsub_comm_ineq (n m k : nat)
  : (n + k) - m <= (n - m) + k.
Proof. 
  simple_induction k k IHk.
  - destruct (nat_add_zero_r n)^, (nat_add_zero_r (n - m))^; constructor.
  - destruct (nat_add_succ_r n k)^.
    refine (leq_trans (nataddsub_comm_ineq_lemma (n+k) m) _).
    destruct (nat_add_succ_r (n - m) k)^.
    now apply leq_succ.
Defined.

Proposition nat_sub_add_ineq (n m : nat) : n <= n - m + m.
Proof.
  destruct (@leq_dichotomy m n) as [l | gt].
  - destruct (nataddsub_comm _ _ m l)^.
    destruct (nat_add_sub_cancel_r n m)^.
    apply leq_refl; done.
  - apply leq_lt in gt.
    destruct (equiv_nat_sub_leq _)^.
    assumption.
Defined.

Proposition i_lt_n_sum_m (n m i : nat)
  : i < n - m -> m <= n.
Proof.
  revert m i; simple_induction n n IHn.
  - intros m i l. simpl in l. contradiction (not_lt_zero_r _ _).
  - intros m i l. destruct m.
    + apply leq_zero_l.
    + apply leq_succ. simpl in l. apply (IHn m i l).
Defined.
  
Proposition nataddsub_assoc_implication (n : nat) {m k z : nat}
  : (k <= m) -> n + (m - k) = z -> n + m - k = z.
Proof.
  intro H.
  destruct (symmetric_paths _ _ (nataddsub_assoc n H)); done.
Defined.

Proposition nat_add_sub_eq (n : nat) {k: nat}
  : (k <= n) -> k + (n - k) = n.
Proof.
  intro H.
  destruct (symmetric_paths _ _ (nataddsub_assoc k H));
  destruct (nat_add_comm n k); exact (nat_add_sub_cancel_r _ _).
Defined.

Proposition predeqminus1 { n : nat } : n - 1 = nat_pred n.
Proof.
  simple_induction' n.
  - reflexivity.
  - apply nat_sub_zero_r.
Defined.

Proposition predn_leq_n (n : nat) : nat_pred n <= n.
Proof.
  destruct n; exact _.
Defined.

Proposition S_predn (n i: nat) : (i < n) -> S(nat_pred n) = n.
Proof.
  simple_induction' n; intros l.
  - contradiction (not_lt_zero_r i).
  - reflexivity.
Defined.

Proposition pred_equiv (k n : nat) : k < n -> k < S (nat_pred n).
Proof. 
  intro ineq; destruct n.
  - contradiction (not_lt_zero_r _ _).
  - assumption.
Defined.

Proposition n_leq_pred_Sn (n : nat) : n <= S (nat_pred n).
Proof. 
  destruct n; exact _.
Defined.

Proposition leq_implies_pred_lt (i n k : nat)
  : (n > i) -> n <= k -> nat_pred n < k.
Proof.
  intro ineq; destruct n.
  - contradiction (not_lt_zero_r i).
  - intro; assumption.
Defined.
  
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

Proposition j_geq_0_lt_implies_pred_geq (i j k : nat)
  : i < j -> k.+1 <= j -> k <= nat_pred j.
Proof.
  intros l ineq.
  destruct j.
  - contradiction (not_lt_zero_r i).
  - now simpl; apply leq_succ'.
Defined.

(** TODO: move, rename *)
Proposition pred_gt_implies_lt (i j : nat)
  : i < nat_pred j -> i.+1 < j.
Proof.
  intros ineq.
  assert (H := leq_succ ineq). assert (i < j) as X. {
    apply (@lt_leq_trans _ (nat_pred j) _);
      [assumption  | apply predn_leq_n].
  }
  destruct (symmetric_paths _ _ (S_predn _ _ X)) in H.
  assumption.
Defined.

(** TODO: move, rename *)
Proposition pred_preserves_lt {i n: nat} (p : i < n) m
  : (n < m) -> (nat_pred n < nat_pred m).
Proof.
  intro l.
  apply leq_succ'. destruct (symmetric_paths _ _ (S_predn n i _)).
  set (k :=  transitive_lt i n m p l).
  destruct (symmetric_paths _ _ (S_predn m i _)).
  assumption.
Defined.

(** TODO: move, rename *)
Proposition natsubpreservesleq { n m k : nat }
  : n <= m -> n - k <= m - k.
Proof.
  simple_induction k k IHk.
  - destruct (symmetric_paths _ _ (nat_sub_zero_r n)),
      (symmetric_paths _ _ (nat_sub_zero_r m)); done.
  - intro l. change (k.+1) with (1 + k).
    destruct (nat_add_comm k 1).
    destruct (symmetric_paths _ _ (nat_sub_add n k 1)).
    destruct (symmetric_paths _ _ (nat_sub_add m k 1)).
    destruct (symmetric_paths _ _ (@predeqminus1 (n -k))).
    destruct (symmetric_paths _ _ (@predeqminus1 (m -k))).
    apply leq_pred, IHk. exact l.
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
Proposition natpmswap1 (k m n : nat)
  : n <= k -> k < n + m -> k - n < m.
Proof.
  intros l q.
  assert (q' : k - n + n < m + n) by
    (destruct (nat_add_sub_l_cancel l)^;
     destruct (nat_add_comm n m);
     assumption).
  exact (lt_reflects_add_r _ q').
Defined.

(** TODO: move, rename *)
Proposition natpmswap2 (k m n : nat)
  : n <= k -> k - n <= m -> k <= n + m.
Proof.
  intros l q.
  apply (nat_add_l_monotone n) in q.
  destruct (nataddsub_assoc n l)^ in q.
  destruct (nat_add_sub_cancel_l k n)^ in q;
    assumption.
Defined.

(** TODO: move, rename *)
Proposition natpmswap3 (k m n : nat)
  : k <= n -> m <= n - k -> k + m <= n.
Proof.
  intros ineq qe.
  apply (nat_add_l_monotone k) in qe.
  destruct (nataddsub_assoc k ineq)^ in qe.
  destruct (nat_add_sub_cancel_l n k)^ in qe;
    assumption.
Defined.

(** TODO: move, rename *)
Proposition natpmswap4 (k m n : nat)
  : k - n < m -> k < n + m.
Proof.
  intro l; apply (nat_add_r_strictly_monotone n) in l.
  destruct (nat_add_comm m n).
  now rapply (leq_lt_trans (nat_sub_add_ineq _ _)).
Defined.

(** TODO: move, rename *)
Proposition n_leq_m_n_leq_plus_m_k (n m k : nat)
  : n <= m -> n <= m + k.
Proof.
  intro l; apply (leq_trans l); exact (leq_add_l m k).
Defined.

(** TODO: move, rename *)
Proposition strong_induction (P : nat -> Type)
  : (forall n : nat, (forall m : nat,  (m < n) -> P m) -> P n) ->
  forall n : nat, P n.
Proof.
  intro a.
  assert (forall n m: nat, m < n -> P m) as X. {
    simple_induction n n IHn.
    - intros m l. contradiction (not_lt_zero_r m).
    - intros m l. apply leq_succ' in l.
      destruct l as [ | n].
      + apply a; intros ? ?; now apply IHn.
      + now apply (IHn m), leq_succ.
  }
  intro n. apply (X (n.+1) n), (leq_refl n.+1).
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
  - now constructor.
Defined.

Proposition increasing_geq_n_0 (n : nat) : increasing_geq n 0.
Proof.
  simple_induction n n IHn.
  - constructor.
  - induction IHn.
    + constructor; now constructor.
    + constructor; now assumption.
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
      destruct (symmetric_paths _ _ (nat_sub_add n k 1)).
      destruct (symmetric_paths _ _ (@predeqminus1 (n - k))).
      apply increasing_geq_S.
      unfold ">", "<" in *.
      apply lt_sub_gt_0 in g. 
      now (destruct (symmetric_paths _ _ (S_predn (n - k) 0 _))).
Defined.

Lemma ineq_sub' (n k : nat) : k < n -> n - k = (n - k.+1).+1.
Proof.
  intro ineq.
  destruct n.
  - contradiction (not_lt_zero_r k).
  - change (n.+1 - k.+1) with (n - k). apply leq_succ' in ineq.
    apply (nataddsub_assoc_lemma _).
Defined.
  
Lemma ineq_sub (n m : nat) : n <= m -> m - (m - n) = n.
Proof.
  revert m; simple_induction n n IHn.
  - intros. destruct (symmetric_paths _ _ (nat_sub_zero_r m)),
      (symmetric_paths _ _ (nat_sub_cancel m));
      reflexivity.
  - intros m ineq. change (m - n.+1) with (m - (1 + n)).
    (destruct (nat_add_comm n 1)).
    destruct (symmetric_paths _ _ (nat_sub_add m n 1)). 
    destruct (S_predn (m - n) 0 (lt_sub_gt_0 _ _ ineq)); simpl;
      destruct (symmetric_paths _ _ (nat_sub_zero_r (nat_pred (m - n)))).
    assert (0 < m - n) as dp by exact (lt_sub_gt_0 _ _ ineq).
    assert (nat_pred (m - n) < m) as sh by
        ( unfold "<";
          destruct (symmetric_paths _ _ (S_predn _ 0 _));
          exact sub_less).
    destruct (symmetric_paths _ _ (ineq_sub' _ _ _)).
    destruct (symmetric_paths _ _ (S_predn _ 0 _)).
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
  - contradiction (lt_irrefl m (lt_leq_trans g ineq)).
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
