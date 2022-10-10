Require Import Basics.
Require Import Basics.Tactics.
Require Import Types.Bool.
Require Import Types.Sum.
Require Import Basics.Utf8.
Require Import Basics.Nat.
Require Import Basics.Decidable.
Require Import Spaces.Nat.
Local Close Scope trunc_scope.
  
Local Open Scope nat_scope.
Ltac nat_absurd_trivial :=
  match goal with
  | [ H : ?n < 0 |- _ ] => contradiction (not_lt_n_0 n)
  | [ H : 0 > ?n |- _ ] => contradiction (not_lt_n_0 n)
  | [ H : ?n > ?n |- _ ] => contradiction (not_lt_n_n n)
  | [ H : ?n < ?n |- _ ] => contradiction (not_lt_n_n n)
  end.

Global Hint Resolve not_lt_n_n : nat.
Global Hint Resolve not_lt_n_0 : nat.
Global Hint Resolve not_leq_Sn_0 : nat.
Global Hint Extern 2 => nat_absurd_trivial : nat.
(* This is defined so that it can be added to the nat auto hint database. *)
Proposition eq_nat_sym : forall n m : nat,  n = m -> m = n.
Proof.
  intros n m; exact (symmetric_paths n m).
Defined.

Global Hint Resolve eq_nat_sym | 5 : nat.
Global Hint Resolve leq_0_n : nat.

Global Hint Resolve leq_trans : nat.

Local Definition transitive_paths_nat := @transitive_paths nat.

Global Hint Resolve transitive_paths_nat : nat.
Global Hint Resolve leq_antisym : nat.

Proposition nat_add_assoc : forall n m k : nat, n + (m + k) = (n + m) + k.
Proof.
  intro n; induction n. 
  - reflexivity.
  - intros m k. change (n.+1 + (m + k)) with (n + (m + k)).+1.
    apply (transitive_paths _ _ _ (nat_add_n_Sm _ _)).
    change (m + k).+1 with (m.+1 + k);
    change (n.+1 + m) with (n + m).+1.
    apply (transitive_paths _ _ _ (IHn m.+1 k)).
    apply (ap (fun zz => zz + k)).
    apply symmetric_paths, nat_add_n_Sm. 
Defined.

Proposition not_lt_implies_geq {n m : nat} : ~(n < m) -> m <= n.
Proof.
  intros not_lt.
  destruct (@leq_dichot m n); [ assumption | contradiction].
Defined.

Proposition not_leq_implies_gt {n m : nat} : ~(n <= m) -> m < n.
Proof.
  intros not_leq. 
  destruct (@leq_dichot n m); [ contradiction | assumption].
Defined.

Proposition lt_implies_not_geq {n m : nat} : (n < m) -> ~(m <= n).
Proof.
  intros ineq1 ineq2.
  contradiction (not_lt_n_n n). by apply (leq_trans ineq1).
Defined.

Proposition leq_implies_not_gt {n m : nat} : (n <= m) -> ~(m < n).
Proof.
  intros ineq1 ineq2.
  contradiction (not_lt_n_n n); by refine (leq_trans _ ineq2).
Defined.

Ltac convert_to_positive :=
  match goal with
  | [ H : ~ (?n < ?m) |- _] =>  apply not_lt_implies_geq in H
  | [ H : ~ (?n <= ?m) |- _] => apply not_leq_implies_gt in H
  | [|- ~ (?n < ?m) ] => apply leq_implies_not_gt
  | [|- ~ (?n <= ?m) ] => apply lt_implies_not_geq
  end.

Global Hint Extern 2 => convert_to_positive : nat.

(* Because of the inductive definition of <=, 
   one can destruct the proof and get a judgemental identification 
   between n and m rather than a propositional one,
   which may be preferable to the following lemma. *)

Proposition leq_split {n m : nat} : (n <= m) -> sum (n < m) (n = m).
Proof.
  intro l. induction l.
  - now right.
  - left. exact (leq_S_n' _ _ l).
Defined.

Proposition diseq_implies_lt : forall n m : nat, n <> m -> sum (n < m) (n > m).
Proof.
  intros n m diseq.
  destruct (dec (n < m)) as [| a]; [ now left |].
  right. destruct (@leq_dichot n m) as [n_leq_m | gt]; [ | assumption].
  destruct n_leq_m; [ now contradiction diseq | contradiction a; now apply leq_S_n']. 
Defined.

Proposition lt_implies_diseq : forall n m : nat, n < m -> (n <> m).
Proof.
  intros n m ineq eq. rewrite eq in ineq. contradiction (not_lt_n_n m).
Defined.

Global Hint Resolve lt_implies_diseq : nat.

Proposition n_lt_Sn : forall n : nat, n < n.+1.
Proof.
  intro n; exact (leq_n n.+1).
Defined.

Proposition leq_S' : forall n m : nat, n.+1 <= m -> n <= m.
Proof.
  intros n m l.
  now apply leq_S_n, leq_S.
Defined.

Ltac easy_eq_to_ineq :=
  match goal with
  | [ H : ?x = ?n    |- ?x <= ?n ] => destruct H; constructor
  | [ H : ?x.+1 = ?n |- ?x <= ?n ] => rewrite <- H; constructor; constructor
  | [ H : ?x.+1 = ?n |- ?x < ?n  ] => rewrite <- H; apply leq_n
  | [ H : ?x.+2 = ?n |- ?x <= ?n ] => rewrite <- H; apply leq_S';
                                      apply leq_S'; apply leq_n
  | [ H : ?x.+2 = ?n |- ?x < ?n ] => rewrite <- H; apply leq_S_n';
                                      apply leq_S
  end.

Global Hint Extern 3 => easy_eq_to_ineq : nat.
  
Proposition mixed_trans1 : forall n m k : nat, n <= m -> m < k -> n < k.
Proof.
  intros n m k l j. apply leq_S_n' in l. apply (@leq_trans (n.+1) (m.+1) k); trivial. 
Defined.

Ltac leq_trans_resolve :=
  match goal with
  | [ H : ?n <= ?m |- ?n <= ?k ] => apply (leq_trans H)
  | [ H : ?k <= ?m |- ?n <= ?k ] => refine (leq_trans _ H)
  | [ H : ?n <= ?m |- ?n < ?k ] => apply (mixed_trans1 _ _ _ H)
  | [ H : ?m <= ?k |- ?n < ?k ] => refine (leq_trans _ H)
  | [ H : ?m <  ?k |- ?n < ?k ] => refine (mixed_trans1 _ _ _ _ H)
  | [ H : ?n <  ?m |- ?n < ?k ] => apply (leq_trans H)
  end.

Global Hint Extern 2 => leq_trans_resolve : nat.

Proposition mixed_trans2 : forall n m k : nat, n < m -> m <= k -> n < k.
Proof.
  intros n m k l j.  apply (@leq_trans (n.+1) m k); trivial. 
Defined.
Global Hint Resolve mixed_trans1 : nat.
Global Hint Resolve mixed_trans2 : nat.

Proposition sub_n_n : forall n : nat, n - n = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; exact IHn.
Defined.

Proposition sub_n_0 : forall n : nat, n - 0 = n.
Proof.
 destruct n; reflexivity.
Defined.

Ltac rewrite_subn0 :=
  match goal with
  | [ |- context [ ?n - 0 ] ] => rewrite -> sub_n_0
  end.
Ltac rewrite_subnn :=
  match goal with
  | [ |- context [ ?n - ?n ] ] => rewrite -> sub_n_n
  end.

Global Hint Rewrite -> sub_n_0 : nat.
Global Hint Rewrite -> sub_n_n : nat.
Global Hint Resolve sub_n_0 : nat.

Proposition add_n_sub_n_eq : forall m n : nat,  m + n - n = m.
Proof.
  intros m n; destruct m.
  - induction n.
    + reflexivity.
    + assumption.
  - induction n.
    + simpl. destruct (add_n_O m); reflexivity.
    + simpl. destruct (add_n_Sm m n). assumption.
Defined.

Proposition add_n_sub_n_eq' : forall m n : nat,  n + m - n = m.
Proof.
  intros n m.
  destruct (nat_add_comm n m). exact (add_n_sub_n_eq n m).
Defined.
 
Proposition n_lt_m_n_leq_m { n m : nat } : n < m -> n <= m.
Proof.
  intro H. apply leq_S, leq_S_n in H; exact H.
Defined.

Global Hint Resolve n_lt_m_n_leq_m : nat.

Proposition lt_trans : forall n m k : nat, n < m -> m < k -> n < k.
Proof.
  eauto with nat.
Defined.

Proposition not_both_less : forall n m : nat, n < m -> ~(m < n).
Proof.
  intros n m l.
  intros a. contradiction (not_lt_n_n _ (lt_trans _ _ _ l a)).
Defined.  

Proposition n_leq_add_n_k : forall n m : nat, n <= n + m.
Proof.
  induction n.
  - apply leq_0_n.
  - intro; simpl; apply leq_S_n', IHn.
Defined.

Proposition n_leq_add_n_k' : forall n m : nat, n <= m + n.
Proof.
  intros n m.
  induction m.
  - exact(leq_n n).
  - simpl. apply leq_S. assumption.
Defined.    

Proposition natineq0eq0 {n : nat} : n <= 0 -> n = 0.
Proof.
  destruct n.
  - reflexivity.
  - intro. contradiction (not_leq_Sn_0 n).
Defined.

Proposition subsubadd : forall n m k : nat, n - (m + k) = n - m - k.
Proof.
  intro n; induction n.
  - reflexivity.
  - intro m; induction m; intro k.
    + change (0 + k) with k; reflexivity.
    + change (m.+1 + k) with (m + k).+1; apply IHn.
Defined.

Global Hint Resolve subsubadd : nat.
Proposition subsubadd' : forall n m k : nat, n - m - k= n - (m + k).
Proof.
  auto with nat.
Defined.

Definition nleqSm_dichot {n m : nat} : (n <= m.+1) -> sum (n <= m) (n = m.+1).
Proof.
  revert m; induction n.
  - intro. left. exact (leq_0_n m).
  - induction m.
    + intro l. apply leq_S_n, natineq0eq0 in l. right; apply ap; exact l.
    + intro l. apply leq_S_n, IHn in l; induction l as [a | b].
      * left. apply leq_S_n'; exact a.
      * right. apply ap; exact b.
Defined.

Proposition sub_leq_0 : forall n m : nat, n <= m -> n - m = 0.
Proof.
  intros n m l.
  induction l.
  - exact (sub_n_n n).
  - change (m.+1) with (1 + m). destruct n.
    + reflexivity.
    + destruct (nat_add_comm m 1).
      destruct (symmetric_paths _ _ (subsubadd n.+1 m 1)).
      destruct (symmetric_paths _ _ IHl).
      reflexivity.
Defined.

Proposition sub_leq_0_converse : forall n m : nat, n - m = 0 -> n <= m.
Proof.
  intro n; induction n.
  - auto with nat.
  - intros m eq. destruct m.
    + simpl in eq. apply symmetric_paths in eq. contradiction (not_eq_O_S n eq).
    + simpl in eq. apply leq_S_n', IHn, eq.
Defined.

Proposition sub_gt_0_lt : forall n m : nat, n - m > 0 -> m < n.
Proof.
  intros n m ineq.
  destruct (@leq_dichot n m) as [n_leq_m |]; [ | assumption].
  apply sub_leq_0 in n_leq_m.
  contradiction (not_lt_n_n 0). now rewrite n_leq_m in ineq.
Defined.

Proposition lt_sub_gt_0 : forall n m : nat, m < n -> 0 < n - m.
Proof.
  induction n.
  - intros m ineq. contradiction (not_lt_n_0 m).
  - induction m.
    + simpl. easy.
    + simpl. intro ineq. apply leq_S_n in ineq. now apply IHn in ineq.
Defined.

Proposition natminuspluseq : forall n m : nat, n <= m -> (m - n) + n = m.
Proof.
  induction n.
  - intros. destruct m; [reflexivity |]. simpl. apply (ap S), symmetric_paths, add_n_O.
  - intros m l. induction m.
    + contradiction (not_leq_Sn_0 n).
    + simpl. apply leq_S_n, IHn in l.
      destruct (nat_add_n_Sm (m - n) n).
      destruct (symmetric_paths _ _ l).
      reflexivity.
Defined.

Proposition natminusplusineq : forall n m : nat,  n <= n - m + m.
Proof.
  intros n m.
  destruct (@leq_dichot m n) as [ | g].
  - destruct (symmetric_paths _ _ (natminuspluseq _ _ l)); constructor.
  - apply n_lt_m_n_leq_m in g.
    now destruct (symmetric_paths _ _ (sub_leq_0 n m _)).
Defined.
    
Proposition natminuspluseq' : forall n m : nat, n <= m -> n + (m - n) = m.
Proof.
  intros. destruct (symmetric_paths _ _ (nat_add_comm n (m - n))).
  apply natminuspluseq. assumption.
Defined.

Global Hint Rewrite -> natminuspluseq : nat.
Global Hint Rewrite -> natminuspluseq' : nat.

Global Hint Resolve leq_S_n' : nat.

Ltac leq_S_n_in_hypotheses :=
  match goal with
  | [ H : ?n.+1 <= ?m.+1 |- _ ] => apply leq_S_n in H
  | [ H : ?n < ?m.+1 |- _ ] => apply leq_S_n in H
  | [ H : ?m.+1 > ?n |- _ ] => apply leq_S_n in H
  | [ H : ?m.+1 >= ?n.+1 |- _ ] => apply leq_S_n in H
  end.

Global Hint Extern 4 => leq_S_n_in_hypotheses : nat.
                                                     
Proposition nataddpreservesleq { n m k : nat } : n <= m -> n + k <= m + k.
Proof.
  intro l.
  induction k.
  - destruct (add_n_O n), (add_n_O m); exact l.
  - destruct (nat_add_n_Sm n k), (nat_add_n_Sm m k); apply leq_S_n'; exact IHk.
Defined.

Global Hint Resolve nataddpreservesleq : nat.

Proposition nataddpreservesleq' { n m k : nat } : n <= m -> k + n <= k + m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k m)),
    (symmetric_paths _ _ (nat_add_comm k n)). exact nataddpreservesleq.
Defined.

Global Hint Resolve nataddpreservesleq' : nat.

Proposition nataddpreserveslt { n m k : nat } : n < m -> n + k < m + k.
Proof.
  unfold "<".
  change (n + k).+1 with (n.+1 + k).
  generalize (n.+1). intros n' l.
  induction k.
  - destruct (add_n_O n'), (add_n_O m); exact l.
  - destruct (nat_add_n_Sm n' k), (nat_add_n_Sm m k); apply leq_S_n'; exact IHk.
Defined.

Proposition nataddpreserveslt' { n m k : nat } : n < m -> k + n < k + m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k n)),
    (symmetric_paths _ _ (nat_add_comm k m)); exact nataddpreserveslt.
Defined.

Proposition nataddreflectslt { n m k : nat } : n + k < m + k -> n < m.
Proof.
  induction k.
  - destruct (add_n_O n), (add_n_O m); trivial.
  - intro l. destruct (nat_add_n_Sm n k), (nat_add_n_Sm m k) in l.
    apply leq_S_n, IHk in l; exact l.
Defined.

Proposition nataddreflectsleq { n m k : nat } : n + k <= m + k -> n <= m.
Proof.
  destruct n.
  - intros ?; apply leq_0_n.
  - intro a. change (n.+1 + k) with (n + k).+1 in a.
    now apply (@nataddreflectslt n m k).
Defined.

Proposition nataddreflectslt' { n m k : nat } : k + n < k + m -> n < m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k n)),
    (symmetric_paths _ _ (nat_add_comm k m)); exact nataddreflectslt.
Defined.

Proposition nataddreflectsleq' { n m k : nat } : k + n <= k + m -> n <= m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k n)),
    (symmetric_paths _ _ (nat_add_comm k m)); exact nataddreflectsleq.
Defined.

Proposition natsubreflectsleq { n m k : nat } : k <= m -> n - k <= m - k -> n <= m.
Proof.
  intros ineq1 ineq2.
  apply (@nataddpreservesleq _ _ k) in ineq2.
  apply (@leq_trans _ (n - k + k) _ (natminusplusineq _ _)).
  apply (@leq_trans _ (m - k + k)  _ _).
  destruct (symmetric_paths _ _ (natminuspluseq k m ineq1)); easy.
Defined.

Proposition nataddsub_assoc_lemma {k m : nat} : (k <= m) -> m.+1 - k = (m - k).+1.
Proof.
  revert m; induction k.
  - intros m l; simpl. destruct m; reflexivity.
  - induction m.
    + simpl; intro g; contradiction (not_leq_Sn_0 _ g).
    + intro l; apply leq_S_n in l. change (m.+2 - k.+1) with (m.+1 - k).
      change (m.+1 - k.+1) with (m - k).
      exact (IHk _ l).
Defined.

Proposition nataddsub_assoc (n : nat) {m k : nat} : (k <= m) -> n + (m - k) = n + m - k.
Proof.
  revert m k. induction n.
  - reflexivity.
  - intros m k l. change (n.+1 + (m - k)) with (n + (m - k)).+1; change (n.+1 + m) with (n +m).+1.
    destruct k, m; [ reflexivity | reflexivity | contradiction (not_lt_n_0 k _) |].
    simpl "-". apply leq_S_n in l.
    destruct (symmetric_paths _ _ (nat_add_n_Sm n (m - k))).
    destruct  (nataddsub_assoc_lemma l).
    apply (IHn m.+1 k).
    apply leq_S.
    assumption.
Defined.

Proposition nataddsub_comm (n m k : nat) : m <= n -> (n - m) + k = (n + k) - m.
Proof.
  intro l.
  destruct (nat_add_comm k n).
  destruct (nataddsub_assoc k l).
  apply nat_add_comm.
Defined.

Proposition nataddsub_comm_ineq_lemma (n m : nat) : n.+1 - m <= (n - m).+1.
Proof.
  revert m.
  induction n.
  - induction m; [ apply leq_n | apply leq_S; apply leq_n ]. 
  - intro m; induction m.
    + apply leq_n.
    + apply IHn.
Defined.

Proposition nataddsub_comm_ineq (n m k : nat) : (n + k) - m <= (n - m) + k.
Proof. 
  induction k.
  - destruct (add_n_O n), (add_n_O (n - m)); constructor.
  - destruct (add_n_Sm n k).
    refine (leq_trans (nataddsub_comm_ineq_lemma (n+k) m) _).
    destruct (add_n_Sm (n - m) k).
    now apply leq_S_n'.
Defined.

Proposition nat_sub_add_ineq ( n m : nat) : n <= n - m + m.
Proof.
  destruct (@leq_dichot m n) as [ | gt].
  - destruct (symmetric_paths _ _ (nataddsub_comm _ _ m l)).
    destruct (symmetric_paths _ _ (add_n_sub_n_eq n m)). apply leq_refl; done.
  - apply n_lt_m_n_leq_m in gt.
    destruct (symmetric_paths _ _ (sub_leq_0 n m _)).
    assumption.
Defined.

Proposition i_lt_n_sum_m (n m : nat) : forall i, i < n - m -> m <= n.
Proof.
  revert m. induction n.
  - intros m i l. simpl in l. contradiction (not_lt_n_0 _ _).
  - intros m i l. induction m.
    + apply leq_0_n.
    + apply leq_S_n'. simpl in l. apply (IHn m i l).
Defined.
  
Proposition nataddsub_assoc_implication (n : nat) {m k z : nat} : (k <= m) -> n + (m - k) = z -> n + m - k = z.
Proof.
  intro H.
  destruct (symmetric_paths _ _ (nataddsub_assoc n H)); done.
Defined.

Global Hint Resolve nataddsub_assoc_implication : nat.

Proposition nat_add_sub_eq (n : nat) {k: nat} : (k <= n) -> k + (n - k) = n.
Proof.
  intro H.
  destruct (symmetric_paths _ _ (nataddsub_assoc k H));
  destruct (nat_add_comm n k); exact (add_n_sub_n_eq _ _).
Defined.

Global Hint Resolve nat_add_sub_eq : nat.

Proposition predeqminus1 { n : nat } : n - 1 = pred n.
Proof.
  induction n.
  - reflexivity.
  - apply sub_n_0.
Defined.

Proposition predn_leq_n : forall n : nat, pred n <= n.
Proof.
  intro n; case n; [ apply leq_n | intro; apply leq_S; apply leq_n].
Defined.

Global Hint Resolve predn_leq_n : nat.

Proposition S_predn (n i: nat): (i < n) -> S(pred n) = n.
Proof.
  intros l.
  induction n.
  - contradiction (not_lt_n_0 i).
  - reflexivity.
Defined.

Global Hint Rewrite S_predn : nat.
Global Hint Resolve S_predn : nat.
Global Hint Rewrite <- pred_Sn : nat.
Global Hint Resolve leq_n_pred : nat.

Proposition pred_equiv : forall k n, k < n -> k < S (pred n).
Proof. 
  intros k n ineq.
  destruct n.
  - contradiction (not_lt_n_0 _ _).
  - assumption.
Defined.

Proposition n_leq_pred_Sn : forall n, n <= S (pred n).
Proof. 
  destruct n; auto.
Defined.

Proposition leq_implies_pred_lt : forall i n k, (n > i) -> n <= k -> pred n < k.
Proof.
  intros i n k ineq.
  destruct n.
  - contradiction (not_lt_n_0 i).
  - intro; assumption.
Defined.
  
Proposition pred_lt_implies__leq : forall n k, pred n < k ->  n <= k.
Proof.
  intros n k l; destruct n.
  - apply leq_0_n.
  - assumption.
Defined.

Proposition lt_implies_pred_geq : forall i j,  i < j -> i <= pred j.
Proof.
  intros ? ? l.
  apply leq_n_pred in l; assumption.
Defined.
Global Hint Resolve lt_implies_pred_geq : nat.

Proposition j_geq_0_lt_implies_pred_geq : forall i j k,  i < j -> k.+1 <= j -> k <= pred j.
Proof.
  intros i j k l ineq.
  destruct j.
  - contradiction (not_lt_n_0 i).
  - now simpl; apply leq_S_n.
Defined.

Global Hint Resolve lt_implies_pred_geq : nat.

Proposition pred_gt_implies_lt : forall i j, i < pred j -> i.+1 < j.
Proof.
  intros i j ineq.
  assert (H := leq_S_n' _ _ ineq). assert (i < j) as X. {
    apply (@mixed_trans2 _ (pred j) _); [assumption | apply predn_leq_n].
  }
  destruct (symmetric_paths _ _ (S_predn _ _ X)) in H.
  assumption.
Defined.

Proposition pred_preserves_lt {i n: nat} (p : i < n) : forall m, (n < m) -> (pred n < pred m).
Proof.
  intros m l.
  apply leq_S_n. destruct (symmetric_paths _ _ (S_predn n i _)).
  set (k :=  transitive_lt i n m p l).
  destruct (symmetric_paths _ _ (S_predn m i _)).
  assumption.
Defined.

Proposition natsubpreservesleq { n m k : nat } : n <= m -> n - k <= m - k.
Proof.
  induction k.
  - destruct (symmetric_paths _ _ (sub_n_0 n)), (symmetric_paths _ _ (sub_n_0 m)); done.
  - intro l. change (k.+1) with (1 + k). destruct (nat_add_comm k 1).
    destruct (symmetric_paths _ _ (subsubadd n k 1)).
    destruct (symmetric_paths _ _ (subsubadd m k 1)).
    destruct (symmetric_paths _ _ (@predeqminus1 (n -k))).
    destruct (symmetric_paths _ _ (@predeqminus1 (m -k))).
    apply leq_n_pred, IHk. exact l.
Defined.

Global Hint Resolve natsubpreservesleq : nat.

Proposition sub_less { n k : nat } : n - k <= n.
Proof.
  revert k.
  induction n.
  - intros; apply leq_0_n.
  - induction k.
    + apply leq_n.
    + simpl; apply (@leq_trans _ n _); [ apply IHn | apply leq_S, leq_n].
Defined.

Global Hint Resolve sub_less : nat.
Global Hint Resolve leq_S_n' : nat.

Proposition sub_less_strict { n k : nat } : 0 < n -> 0 < k -> n - k < n.
Proof.
  intros l l'.
  unfold "<".
  destruct k, n;
  try (contradiction (not_lt_n_0 _ _)).
  simpl; apply leq_S_n', sub_less.
Defined.

Proposition natpmswap1 : forall k m n, n <= k -> k < n + m -> k - n < m.
Proof.
  intros k m n l q.
  assert (q' : k - n + n < m + n) by
    (destruct (symmetric_paths _ _ (natminuspluseq n k l));
     destruct (nat_add_comm n m);
     assumption).
  exact (nataddreflectslt q').
Defined.

Global Hint Resolve natpmswap1 : nat.

Proposition natpmswap2 : forall k m n, n <= k -> k - n <= m -> k <= n + m.
Proof.
  intros k m n l q.
  apply (@nataddpreservesleq' (k - n) m n) in q.
  destruct (symmetric_paths _ _ (nataddsub_assoc n l)) in q.
  destruct (symmetric_paths _ _ (add_n_sub_n_eq' k n)) in q; assumption.
Defined.

Global Hint Resolve natpmswap2 : nat.

Proposition natpmswap3 : forall k m n : nat, k <= n -> m <= n - k -> k + m <= n.
Proof.
  intros k m n ineq qe.
  apply (@nataddpreservesleq' m (n - k) k) in qe.
  destruct (symmetric_paths _ _ (nataddsub_assoc k ineq)) in qe.
  destruct (symmetric_paths _ _ (add_n_sub_n_eq' n k)) in qe;
    assumption.
Defined.

Global Hint Resolve natpmswap3 : nat.

Proposition natpmswap4 : forall k m n, k - n < m -> k < n + m.
Proof.
  intros k m n l.
  apply (@nataddpreserveslt (k - n) m n) in l.
  destruct (nat_add_comm m n).
  now apply (mixed_trans1 k (k - n + n) (m + n) (nat_sub_add_ineq _ _)).
Defined.

Global Hint Resolve natpmswap4 : nat.

Proposition n_leq_m_n_leq_plus_m_k : forall n m k, n <= m -> n <= m + k.
Proof.
  intros n m k; intro l; apply (leq_trans l); exact (n_leq_add_n_k m k).
Defined.

Proposition nat_add_bifunctor : forall n n' m m' : nat, n <= m -> n' <= m' -> n + n' <= m + m'.
Proof.
  intro n; induction n.
  - intros n' m m' l l'. simpl. apply (leq_trans l'). exact (n_leq_add_n_k' m' m).
  - intros n' m; induction m.
    + intros. contradiction (not_leq_Sn_0 n).
    + intros m' l l'. apply leq_S_n in l. simpl. apply leq_S_n', IHn.
      * exact l.
      * exact l'.
Defined.

Global Hint Resolve nat_add_bifunctor : nat.
Global Hint Resolve nataddpreserveslt : nat.
Global Hint Resolve nataddpreservesleq' : nat.
Global Hint Resolve nataddpreserveslt' : nat.
Global Hint Resolve natineq0eq0 : nat.
Global Hint Rewrite <- add_n_O : nat.
Global Hint Rewrite -> add_O_n : nat.
Global Hint Resolve n_leq_add_n_k : nat.
Global Hint Immediate add_n_sub_n_eq : nat.
Global Hint Resolve n_leq_m_n_leq_plus_m_k : nat.
Global Hint Immediate add_n_sub_n_eq' : nat.
Global Hint Rewrite -> add_n_sub_n_eq : nat.
Global Hint Rewrite -> add_n_sub_n_eq' : nat.


Ltac autorewrite_or_fail := progress ltac:(autorewrite with nat).

Global Hint Extern 7 => autorewrite_or_fail : nat.

Global Hint Rewrite -> nataddsub_assoc : nat.

Proposition strong_induction (P : nat -> Type) :
  (forall n : nat, (forall m : nat,  (m < n) -> P m) -> P n) ->
  forall n : nat, P n.
Proof.
  intro a.
  assert (forall n m: nat, m < n -> P m) as X. {
    induction n.
    - intros m l. contradiction (not_lt_n_0 m).
    - intros m l. apply leq_S_n in l.
      destruct l as [ | n].
      + apply a; intros t L; now apply IHn.
      + now apply (IHn m), leq_S_n'.
  }
  intro n. apply (X (n.+1) n), (leq_n n.+1).
Defined.

Inductive left_handed_leq : nat -> nat -> Type :=
| left_handed_leq_n (n : nat) : left_handed_leq n n
| left_handed_leq_S (n m : nat) : left_handed_leq n.+1 m -> left_handed_leq n m.

Proposition left_handed_leq_S_n (n m : nat) : left_handed_leq n m -> left_handed_leq n.+1 m.+1.
Proof.
  intro a.
  induction a.
  - constructor.
  - now constructor.
Defined.

Proposition left_handed_leq_0_n (n :nat) : left_handed_leq 0 n.
Proof.
  induction n.
  - constructor.
  - induction IHn.
    + constructor; now constructor.
    + constructor; now assumption.
Defined.

Definition least_such_that (P : nat -> Type) {T : forall n, Decidable (P n)}
           (k : nat) (p : P k) : nat.
Proof.
  assert (t := left_handed_leq_0_n k).
  induction t. 
  - exact n.
  - destruct (T n).
    + exact n.
    + exact (IHt p).
Defined.

Proposition least_such_that_P_holds (P : nat -> Type) {T : forall n, Decidable (P n)}
           (n : nat) (p : P n) : (P (least_such_that P n p)).
Proof.
  unfold least_such_that. induction (left_handed_leq_0_n n).
  - assumption.
  - simpl. destruct (T n).
    + assumption.
    + apply IHl.
Defined.
Proposition least_such_that_P_is_least (P : nat -> Type) {T : forall n, Decidable (P n)}
           (n : nat) (p : P n) : 
  (forall k : nat, P k -> (least_such_that P n p) <= k).
Proof.
  intros k Pk. unfold least_such_that.
  set (Q := left_handed_leq_rect _ _ _). generalize (left_handed_leq_0_n n); intro l.
  cut (forall x : nat, forall l0 : left_handed_leq x n, x <= k -> Q x n l0 p <= k). {
    intro KT. specialize KT with 0 l; apply (KT (leq_0_n k)). }
  intros x l0 ineq. induction l0 as [| x n].
  - assumption.
  - simpl. destruct (T x).
    + assumption.
    + apply IHl0. { apply (left_handed_leq_0_n n). } destruct ineq.
      * contradiction.
      * apply leq_S_n'; assumption.
Defined.

Lemma left_handed_leq_minus : forall n k : nat, left_handed_leq (n - k) n.
Proof.
  induction k.
  - destruct (symmetric_paths _ _ (sub_n_0 n)); constructor.
  - destruct (@leq_dichot n k) as [l | g].
    + destruct (symmetric_paths _ _ (sub_leq_0 _ _ _)) in IHk. apply leq_S in l.
      destruct (symmetric_paths _ _ (sub_leq_0 _ _ _)). exact IHk.
    + change k.+1 with (1 + k). destruct (nat_add_comm k 1).
      Check subsubadd.
      destruct (symmetric_paths _ _ (subsubadd n k 1)).
      destruct (symmetric_paths _ _ (@predeqminus1 (n - k))).
      apply left_handed_leq_S.
      unfold ">", "<" in *.
      apply lt_sub_gt_0 in g. 
      now (destruct (symmetric_paths _ _ (S_predn (n - k) 0 _))).
Defined.

Lemma ineq_sub' : forall n k : nat, k < n -> n - k = (n - k.+1).+1.
Proof.
  intros n k ineq.
  destruct n.
  - contradiction (not_lt_n_0 k).
  - change (n.+1 - k.+1) with (n - k). apply leq_S_n in ineq.
    apply (nataddsub_assoc_lemma _).
Defined.
  
Lemma ineq_sub : forall n m : nat, n <= m -> m - (m - n) = n.
Proof.
  intro n; induction n.
  - intros. destruct (symmetric_paths _ _ (sub_n_0 m)), (symmetric_paths _ _ (sub_n_n m));
      reflexivity.
  - intros m ineq. change (m - n.+1) with (m - (1 + n)). (destruct (nat_add_comm n 1)).
    destruct (symmetric_paths _ _ (subsubadd m n 1)). 
    destruct (S_predn (m - n) 0 (lt_sub_gt_0 _ _ ineq)); simpl;
      destruct (symmetric_paths _ _ (sub_n_0 (pred (m - n)))).
    assert (0 < m - n) as dp by exact (lt_sub_gt_0 _ _ ineq).
    assert (pred (m - n) < m) as sh by
        ( unfold "<"; destruct (symmetric_paths _ _ (S_predn _ 0 _));
          exact sub_less).
    destruct (symmetric_paths _ _ (ineq_sub' _ _ _)).
    destruct (symmetric_paths _ _ (S_predn _ 0 _)).
    apply (ap S), IHn, leq_S', ineq.
Defined.                                 
  
Proposition leq_equivalent : forall n m : nat, n <= m <-> left_handed_leq n m.
Proof.
  split.
  - intro ineq. induction ineq.
    + constructor.
    + apply left_handed_leq_S_n in IHineq; constructor; assumption.
  - intro a.
    induction a.
    + constructor.
    + exact (leq_S' _ _ _).
Defined.

Definition leq_wrapper {n m : nat} : n <= m -> n <= m.
Proof.
  intro ineq.
  destruct (@leq_dichot n m) as [| g].
  - exact l.
  - contradiction (not_lt_n_n m (@mixed_trans2 _ _ _ g ineq)).
Defined.

Proposition symmetric_rel_total_order (R : nat -> nat -> Type)
            {p : Symmetric R} {p' : Reflexive R}
  : (forall n m : nat, n < m -> R n m) -> (forall n m : nat, R n m).
Proof.
  intros A n m.
  destruct (@leq_dichot m n) as [m_leq_n | m_gt_n].
  - apply symmetry. destruct m_leq_n.
    + apply reflexivity.
    + apply A. apply leq_S_n'. assumption.
  - apply A, m_gt_n.
Defined.                             
