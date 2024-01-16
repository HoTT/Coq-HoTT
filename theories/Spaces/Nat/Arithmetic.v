Require Import Basics.
Require Import Spaces.Nat.Core.
  
Local Set Universe Minimization ToSet.

Local Close Scope trunc_scope.
Local Open Scope nat_scope.

Ltac nat_absurd_trivial :=
  unfold ">" in *; unfold "<" in *;
  match goal with
  | [ H : ?n.+1 <= 0 |- _ ] => contradiction (not_leq_Sn_0 n H)
  | [ H : ?n.+1 <= ?n |- _ ] => contradiction (not_lt_n_n n H)
  | [ H1 : ?k.+1 <= ?n |- _ ] =>
      match goal with
      | [ H2 : ?n <= ?k |- _] =>
          contradiction (not_leq_Sn_n k (@leq_trans _ _ _ H1 H2))
      end
  end.

#[export] Hint Resolve not_lt_n_n : nat.
#[export] Hint Resolve not_lt_n_0 : nat.
#[export] Hint Resolve not_leq_Sn_0 : nat.
#[export] Hint Extern 2 => nat_absurd_trivial : nat.

(** This is defined so that it can be added to the [nat] auto hint database. *)
Local Definition symmetric_paths_nat (n m : nat)
  : n = m -> m = n := @symmetric_paths nat n m.

Local Definition transitive_paths_nat (n m k : nat)
  : n = m -> m = k -> n = k := @transitive_paths nat n m k.

#[export] Hint Resolve symmetric_paths_nat | 5 : nat.
#[export] Hint Resolve transitive_paths_nat : nat.
#[export] Hint Resolve leq_0_n : nat.
#[export] Hint Resolve leq_trans : nat.
#[export] Hint Resolve leq_antisym : nat.

Proposition assoc_nat_add (n m k : nat)
  : n + (m + k) = (n + m) + k.
Proof.
  revert m k; simple_induction n n IHn.
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

#[export] Hint Extern 2 => convert_to_positive : nat.

(** Because of the inductive definition of [<=], one can destruct the proof of [n <= m] and get a judgemental identification between [n] and [m] rather than a propositional one, which may be preferable to the following lemma. *)
Proposition leq_split {n m : nat} : (n <= m) -> sum (n < m) (n = m).
Proof.
  intro l. induction l.
  - now right.
  - left. exact (leq_S_n' _ _ l).
Defined.

Proposition diseq_implies_lt (n m : nat)
  : n <> m -> sum (n < m) (n > m).
Proof.
  intros diseq.
  destruct (dec (n < m)) as [| a]; [ now left |].
  right. destruct (@leq_dichot n m) as [n_leq_m | gt];
    [ | assumption].
  destruct n_leq_m;
    [ now contradiction diseq
    | contradiction a; now apply leq_S_n'].
Defined.

Proposition lt_implies_diseq (n m : nat)
  : n < m -> (n <> m).
Proof.
  intros ineq eq. rewrite eq in ineq.
  contradiction (not_lt_n_n m).
Defined.

#[export] Hint Resolve lt_implies_diseq : nat.

(** This lemma is just for convenience in the case where the user forgets to unfold the definition of [<]. *)
Proposition n_lt_Sn (n : nat) : n < n.+1.
Proof.
  exact (leq_n n.+1).
Defined.

Proposition leq_S' (n m : nat) : n.+1 <= m -> n <= m.
Proof.
  intro l.
  now apply leq_S_n, leq_S.
Defined.

Ltac easy_eq_to_ineq :=
  match goal with
  | [ H : ?x = ?n    |- ?x <= ?n ] => destruct H; constructor
  | [ H : ?x.+1 = ?n |- ?x <= ?n ] => rewrite <- H; constructor;
                                      constructor
  | [ H : ?x.+1 = ?n |- ?x < ?n  ] => rewrite <- H; apply leq_n
  | [ H : ?x.+2 = ?n |- ?x <= ?n ] => rewrite <- H; apply leq_S';
                                      apply leq_S'; apply leq_n
  | [ H : ?x.+2 = ?n |- ?x < ?n ] => rewrite <- H; apply leq_S_n';
                                      apply leq_S
  end.

#[export] Hint Extern 3 => easy_eq_to_ineq : nat.
  
Proposition mixed_trans1 (n m k : nat)
  : n <= m -> m < k -> n < k.
Proof.
  intros l j. apply leq_S_n' in l.
  apply (@leq_trans (n.+1) (m.+1) k); trivial. 
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

#[export] Hint Extern 2 => leq_trans_resolve : nat.

Proposition mixed_trans2 (n m k : nat)
  : n < m -> m <= k -> n < k.
Proof.
  intros l j. apply (@leq_trans (n.+1) m k); trivial. 
Defined.

#[export] Hint Resolve mixed_trans1 : nat.
#[export] Hint Resolve mixed_trans2 : nat.

Proposition sub_n_n (n : nat) : n - n = 0.
Proof.
  simple_induction n n IHn.
  - reflexivity.
  - simpl; exact IHn.
Defined.

Proposition sub_n_0 (n : nat) : n - 0 = n.
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

#[export] Hint Rewrite -> sub_n_0 : nat.
#[export] Hint Rewrite -> sub_n_n : nat.
#[export] Hint Resolve sub_n_0 : nat.

Proposition add_n_sub_n_eq (m n : nat) : m + n - n = m.
Proof.
  destruct m.
  - simple_induction' n.
    + reflexivity.
    + assumption.
  - simple_induction' n.
    + simpl. destruct (add_n_O m); reflexivity.
    + simpl. destruct (add_n_Sm m n). assumption.
Defined.

Proposition add_n_sub_n_eq' (m n : nat) : n + m - n = m.
Proof. 
  destruct (nat_add_comm m n). exact (add_n_sub_n_eq m n).
Defined.
 
Proposition n_lt_m_n_leq_m { n m : nat } : n < m -> n <= m.
Proof.
  intro H. apply leq_S, leq_S_n in H; exact H.
Defined.

#[export] Hint Resolve n_lt_m_n_leq_m : nat.

Proposition lt_trans (n m k : nat) : n < m -> m < k -> n < k.
Proof.
  eauto with nat.
Defined.

Proposition not_both_less (n m : nat) : n < m -> ~(m < n).
Proof.
  intros l a; contradiction (not_lt_n_n _ (lt_trans _ _ _ l a)).
Defined.  

Proposition n_leq_add_n_k (n m : nat) : n <= n + m.
Proof.
  simple_induction n n IHn.
  - apply leq_0_n.
  - simpl; apply leq_S_n', IHn.
Defined.

Proposition n_leq_add_n_k' (n m : nat) : n <= m + n.
Proof.
  simple_induction' m.
  - exact(leq_n n).
  - simpl. apply leq_S. assumption.
Defined.

Proposition natineq0eq0 {n : nat} : n <= 0 -> n = 0.
Proof.
  destruct n.
  - reflexivity.
  - intro. contradiction (not_leq_Sn_0 n).
Defined.

Proposition subsubadd (n m k : nat) : n - (m + k) = n - m - k.
Proof.
  revert m k; simple_induction n n IHn.
  - reflexivity.
  - intro m; destruct m; intro k.
    + change (0 + k) with k; reflexivity.
    + change (m.+1 + k) with (m + k).+1; apply IHn.
Defined.

#[export] Hint Resolve subsubadd : nat.

Proposition subsubadd' (n m k : nat) : n - m - k = n - (m + k).
Proof.
  auto with nat.
Defined.

Definition nleqSm_dichot {n m : nat}
  : (n <= m.+1) -> sum (n <= m) (n = m.+1).
Proof.
  revert m; simple_induction n n IHn.
  - intro. left. exact (leq_0_n m).
  - destruct m.
    + intro l. apply leq_S_n, natineq0eq0 in l.
      right; apply ap; exact l.
    + intro l. apply leq_S_n, IHn in l; destruct l as [a | b].
      * left. apply leq_S_n'; exact a.
      * right. apply ap; exact b.
Defined.

Proposition sub_leq_0 (n m : nat) : n <= m -> n - m = 0.
Proof.
  intro l; induction l.
  - exact (sub_n_n n).
  - change (m.+1) with (1 + m). destruct n.
    + reflexivity.
    + destruct (nat_add_comm m 1).
      destruct (symmetric_paths _ _ (subsubadd n.+1 m 1)).
      destruct (symmetric_paths _ _ IHl).
      reflexivity.
Defined.

Proposition sub_leq_0_converse (n m : nat) : n - m = 0 -> n <= m.
Proof.
  revert m; simple_induction n n IHn.
  - auto with nat.
  - intros m eq. destruct m.
    + simpl in eq. apply symmetric_paths in eq.
      contradiction (not_eq_O_S n eq).
    + simpl in eq. apply leq_S_n', IHn, eq.
Defined.

Proposition sub_gt_0_lt (n m : nat) : n - m > 0 -> m < n.
Proof.
  intro ineq.
  destruct (@leq_dichot n m) as [n_leq_m |]; [ | assumption].
  apply sub_leq_0 in n_leq_m.
  contradiction (not_lt_n_n 0). now rewrite n_leq_m in ineq.
Defined.

Proposition lt_sub_gt_0 (n m : nat) : m < n -> 0 < n - m.
Proof.
  revert m; simple_induction n n IHn.
  - intros m ineq. contradiction (not_lt_n_0 m).
  - destruct m.
    + simpl. easy.
    + simpl. intro ineq. apply leq_S_n in ineq.
      now apply IHn in ineq.
Defined.

Proposition natminuspluseq (n m : nat)
  : n <= m -> (m - n) + n = m.
Proof.
  revert m; simple_induction n n IHn.
  - intros. destruct m; [reflexivity |]. simpl.
    apply (ap S), symmetric_paths, add_n_O.
  - intros m l. destruct m.
    + contradiction (not_leq_Sn_0 n).
    + simpl. apply leq_S_n, IHn in l.
      destruct (nat_add_n_Sm (m - n) n).
      destruct (symmetric_paths _ _ l).
      reflexivity.
Defined.

Proposition natminusplusineq (n m : nat) : n <= n - m + m.
Proof.
  destruct (@leq_dichot m n) as [l | g].
  - destruct (symmetric_paths _ _ (natminuspluseq _ _ l));
      constructor.
  - apply n_lt_m_n_leq_m in g.
    now destruct (symmetric_paths _ _ (sub_leq_0 n m _)).
Defined.

Proposition natminuspluseq' (n m : nat)
  : n <= m -> n + (m - n) = m.
Proof.
  intros. destruct (symmetric_paths _ _ (nat_add_comm n (m - n))).
  apply natminuspluseq. assumption.
Defined.

#[export] Hint Rewrite -> natminuspluseq : nat.
#[export] Hint Rewrite -> natminuspluseq' : nat.

#[export] Hint Resolve leq_S_n' : nat.

Ltac leq_S_n_in_hypotheses :=
  match goal with
  | [ H : ?n.+1 <= ?m.+1 |- _ ] => apply leq_S_n in H
  | [ H : ?n < ?m.+1 |- _ ] => apply leq_S_n in H
  | [ H : ?m.+1 > ?n |- _ ] => apply leq_S_n in H
  | [ H : ?m.+1 >= ?n.+1 |- _ ] => apply leq_S_n in H
  end.

#[export] Hint Extern 4 => leq_S_n_in_hypotheses : nat.
                                                     
Proposition nataddpreservesleq { n m k : nat }
  : n <= m -> n + k <= m + k.
Proof.
  intro l.
  simple_induction k k IHk.
  - destruct (add_n_O n), (add_n_O m); exact l.
  - destruct (nat_add_n_Sm n k), (nat_add_n_Sm m k);
      apply leq_S_n'; exact IHk.
Defined.

#[export] Hint Resolve nataddpreservesleq : nat.

Proposition nataddpreservesleq' { n m k : nat }
  : n <= m -> k + n <= k + m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k m)),
    (symmetric_paths _ _ (nat_add_comm k n)).
  exact nataddpreservesleq.
Defined.

#[export] Hint Resolve nataddpreservesleq' : nat.

Proposition nataddpreserveslt { n m k : nat }
  : n < m -> n + k < m + k.
Proof.
  unfold "<".
  change (n + k).+1 with (n.+1 + k).
  generalize (n.+1). intros n' l.
  simple_induction k k IHk.
  - destruct (add_n_O n'), (add_n_O m); exact l.
  - destruct (nat_add_n_Sm n' k), (nat_add_n_Sm m k);
      apply leq_S_n'; exact IHk.
Defined.

Proposition nataddpreserveslt' { n m k : nat }
  : n < m -> k + n < k + m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k n)),
    (symmetric_paths _ _ (nat_add_comm k m));
    exact nataddpreserveslt.
Defined.

Proposition nataddreflectslt { n m k : nat }
  : n + k < m + k -> n < m.
Proof.
  simple_induction k k IHk.
  - destruct (add_n_O n), (add_n_O m); trivial.
  - intro l. destruct (nat_add_n_Sm n k), (nat_add_n_Sm m k) in l.
    apply leq_S_n, IHk in l; exact l.
Defined.

Proposition nataddreflectsleq { n m k : nat }
  : n + k <= m + k -> n <= m.
Proof.
  destruct n.
  - intros ?; apply leq_0_n.
  - intro a. change (n.+1 + k) with (n + k).+1 in a.
    now apply (@nataddreflectslt n m k).
Defined.

Proposition nataddreflectslt' { n m k : nat }
  : k + n < k + m -> n < m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k n)),
    (symmetric_paths _ _ (nat_add_comm k m));
    exact nataddreflectslt.
Defined.

Proposition nataddreflectsleq' { n m k : nat }
  : k + n <= k + m -> n <= m.
Proof.
  destruct (symmetric_paths _ _ (nat_add_comm k n)),
    (symmetric_paths _ _ (nat_add_comm k m));
    exact nataddreflectsleq.
Defined.

Proposition natsubreflectsleq { n m k : nat }
  : k <= m -> n - k <= m - k -> n <= m.
Proof.
  intros ineq1 ineq2.
  apply (@nataddpreservesleq _ _ k) in ineq2.
  apply (@leq_trans _ (n - k + k) _ (natminusplusineq _ _)).
  apply (@leq_trans _ (m - k + k)  _ _).
  destruct (symmetric_paths _ _ (natminuspluseq k m ineq1)); easy.
Defined.

Proposition nataddsub_assoc_lemma {k m : nat}
  : (k <= m) -> m.+1 - k = (m - k).+1.
Proof.
  revert m; simple_induction k k IHk.
  - intros m l; simpl. destruct m; reflexivity.
  - destruct m.
    + simpl; intro g; contradiction (not_leq_Sn_0 _ g).
    + intro l; apply leq_S_n in l.
      change (m.+2 - k.+1) with (m.+1 - k).
      change (m.+1 - k.+1) with (m - k).
      exact (IHk _ l).
Defined.

Proposition nataddsub_assoc (n : nat) {m k : nat}
  : (k <= m) -> n + (m - k) = n + m - k.
Proof.
  revert m k. simple_induction n n IHn.
  - reflexivity.
  - intros m k l.
    change (n.+1 + (m - k)) with (n + (m - k)).+1;
      change (n.+1 + m) with (n +m).+1.
    destruct k, m;
      [ reflexivity
      | reflexivity
      | contradiction (not_lt_n_0 k _)
      | ].
    simpl "-". apply leq_S_n in l.
    destruct (symmetric_paths _ _ (nat_add_n_Sm n (m - k))).
    destruct  (nataddsub_assoc_lemma l).
    apply (IHn m.+1 k).
    apply leq_S.
    assumption.
Defined.

Proposition nataddsub_comm (n m k : nat)
  : m <= n -> (n - m) + k = (n + k) - m.
Proof.
  intro l.
  destruct (nat_add_comm k n).
  destruct (nataddsub_assoc k l).
  apply nat_add_comm.
Defined.

Proposition nataddsub_comm_ineq_lemma (n m : nat)
  : n.+1 - m <= (n - m).+1.
Proof.
  revert m.
  simple_induction n n IHn.
  - simple_induction m m IHm; [ apply leq_n | apply leq_S; apply leq_n ]. 
  - intro m; simple_induction m m IHm.
    + apply leq_n.
    + apply IHn.
Defined.

Proposition nataddsub_comm_ineq (n m k : nat)
  : (n + k) - m <= (n - m) + k.
Proof. 
  simple_induction k k IHk.
  - destruct (add_n_O n), (add_n_O (n - m)); constructor.
  - destruct (add_n_Sm n k).
    refine (leq_trans (nataddsub_comm_ineq_lemma (n+k) m) _).
    destruct (add_n_Sm (n - m) k).
    now apply leq_S_n'.
Defined.

Proposition nat_sub_add_ineq (n m : nat) : n <= n - m + m.
Proof.
  destruct (@leq_dichot m n) as [l | gt].
  - destruct (symmetric_paths _ _ (nataddsub_comm _ _ m l)).
    destruct (symmetric_paths _ _ (add_n_sub_n_eq n m)).
    apply leq_refl; done.
  - apply n_lt_m_n_leq_m in gt.
    destruct (symmetric_paths _ _ (sub_leq_0 n m _)).
    assumption.
Defined.

Proposition i_lt_n_sum_m (n m i : nat)
  : i < n - m -> m <= n.
Proof.
  revert m i; simple_induction n n IHn.
  - intros m i l. simpl in l. contradiction (not_lt_n_0 _ _).
  - intros m i l. destruct m.
    + apply leq_0_n.
    + apply leq_S_n'. simpl in l. apply (IHn m i l).
Defined.
  
Proposition nataddsub_assoc_implication (n : nat) {m k z : nat}
  : (k <= m) -> n + (m - k) = z -> n + m - k = z.
Proof.
  intro H.
  destruct (symmetric_paths _ _ (nataddsub_assoc n H)); done.
Defined.

#[export] Hint Resolve nataddsub_assoc_implication : nat.

Proposition nat_add_sub_eq (n : nat) {k: nat}
  : (k <= n) -> k + (n - k) = n.
Proof.
  intro H.
  destruct (symmetric_paths _ _ (nataddsub_assoc k H));
  destruct (nat_add_comm n k); exact (add_n_sub_n_eq _ _).
Defined.

#[export] Hint Resolve nat_add_sub_eq : nat.

Proposition predeqminus1 { n : nat } : n - 1 = pred n.
Proof.
  simple_induction' n.
  - reflexivity.
  - apply sub_n_0.
Defined.

Proposition predn_leq_n (n : nat) : pred n <= n.
Proof.
  case n; [ apply leq_n | intro; apply leq_S; apply leq_n].
Defined.

#[export] Hint Resolve predn_leq_n : nat.

Proposition S_predn (n i: nat) : (i < n) -> S(pred n) = n.
Proof.
  simple_induction' n; intros l.
  - contradiction (not_lt_n_0 i).
  - reflexivity.
Defined.

#[export] Hint Rewrite S_predn : nat.
#[export] Hint Rewrite <- pred_Sn : nat.

#[export] Hint Resolve S_predn : nat.
#[export] Hint Resolve leq_n_pred : nat.

Proposition pred_equiv (k n : nat) : k < n -> k < S (pred n).
Proof. 
  intro ineq; destruct n.
  - contradiction (not_lt_n_0 _ _).
  - assumption.
Defined.

Proposition n_leq_pred_Sn (n : nat) : n <= S (pred n).
Proof. 
  destruct n; auto.
Defined.

Proposition leq_implies_pred_lt (i n k : nat)
  : (n > i) -> n <= k -> pred n < k.
Proof.
  intro ineq; destruct n.
  - contradiction (not_lt_n_0 i).
  - intro; assumption.
Defined.
  
Proposition pred_lt_implies_leq (n k : nat)
  : pred n < k -> n <= k.
Proof.
  intro l; destruct n.
  - apply leq_0_n.
  - assumption.
Defined.

Proposition lt_implies_pred_geq (i j : nat) : i < j -> i <= pred j.
Proof.
  intro l; apply leq_n_pred in l; assumption.
Defined.

#[export] Hint Resolve lt_implies_pred_geq : nat.

Proposition j_geq_0_lt_implies_pred_geq (i j k : nat)
  : i < j -> k.+1 <= j -> k <= pred j.
Proof.
  intros l ineq.
  destruct j.
  - contradiction (not_lt_n_0 i).
  - now simpl; apply leq_S_n.
Defined.

#[export] Hint Resolve lt_implies_pred_geq : nat.

Proposition pred_gt_implies_lt (i j : nat)
  : i < pred j -> i.+1 < j.
Proof.
  intros ineq.
  assert (H := leq_S_n' _ _ ineq). assert (i < j) as X. {
    apply (@mixed_trans2 _ (pred j) _);
      [assumption  | apply predn_leq_n].
  }
  destruct (symmetric_paths _ _ (S_predn _ _ X)) in H.
  assumption.
Defined.

Proposition pred_preserves_lt {i n: nat} (p : i < n) m
  : (n < m) -> (pred n < pred m).
Proof.
  intro l.
  apply leq_S_n. destruct (symmetric_paths _ _ (S_predn n i _)).
  set (k :=  transitive_lt i n m p l).
  destruct (symmetric_paths _ _ (S_predn m i _)).
  assumption.
Defined.

Proposition natsubpreservesleq { n m k : nat }
  : n <= m -> n - k <= m - k.
Proof.
  simple_induction k k IHk.
  - destruct (symmetric_paths _ _ (sub_n_0 n)),
      (symmetric_paths _ _ (sub_n_0 m)); done.
  - intro l. change (k.+1) with (1 + k).
    destruct (nat_add_comm k 1).
    destruct (symmetric_paths _ _ (subsubadd n k 1)).
    destruct (symmetric_paths _ _ (subsubadd m k 1)).
    destruct (symmetric_paths _ _ (@predeqminus1 (n -k))).
    destruct (symmetric_paths _ _ (@predeqminus1 (m -k))).
    apply leq_n_pred, IHk. exact l.
Defined.

#[export] Hint Resolve natsubpreservesleq : nat.

Proposition sub_less { n k : nat } : n - k <= n.
Proof.
  revert k.
  simple_induction n n IHn.
  - intros; apply leq_0_n.
  - destruct k.
    + apply leq_n.
    + simpl; apply (@leq_trans _ n _);
        [ apply IHn | apply leq_S, leq_n].
Defined.

#[export] Hint Resolve sub_less : nat.
#[export] Hint Resolve leq_S_n' : nat.

Proposition sub_less_strict { n k : nat }
  : 0 < n -> 0 < k -> n - k < n.
Proof.
  intros l l'.
  unfold "<".
  destruct k, n;
  try (contradiction (not_lt_n_0 _ _)).
  simpl; apply leq_S_n', sub_less.
Defined.

Proposition natpmswap1 (k m n : nat)
  : n <= k -> k < n + m -> k - n < m.
Proof.
  intros l q.
  assert (q' : k - n + n < m + n) by
    (destruct (symmetric_paths _ _ (natminuspluseq n k l));
     destruct (nat_add_comm n m);
     assumption).
  exact (nataddreflectslt q').
Defined.

#[export] Hint Resolve natpmswap1 : nat.

Proposition natpmswap2 (k m n : nat)
  : n <= k -> k - n <= m -> k <= n + m.
Proof.
  intros l q.
  apply (@nataddpreservesleq' (k - n) m n) in q.
  destruct (symmetric_paths _ _ (nataddsub_assoc n l)) in q.
  destruct (symmetric_paths _ _ (add_n_sub_n_eq' k n)) in q;
    assumption.
Defined.

#[export] Hint Resolve natpmswap2 : nat.

Proposition natpmswap3 (k m n : nat)
  : k <= n -> m <= n - k -> k + m <= n.
Proof.
  intros ineq qe.
  apply (@nataddpreservesleq' m (n - k) k) in qe.
  destruct (symmetric_paths _ _ (nataddsub_assoc k ineq)) in qe.
  destruct (symmetric_paths _ _ (add_n_sub_n_eq' n k)) in qe;
    assumption.
Defined.

#[export] Hint Resolve natpmswap3 : nat.

Proposition natpmswap4 (k m n : nat)
  : k - n < m -> k < n + m.
Proof.
  intro l; apply (@nataddpreserveslt (k - n) m n) in l.
  destruct (nat_add_comm m n).
  now apply (mixed_trans1 k (k - n + n) (m + n)
               (nat_sub_add_ineq _ _)).
Defined.

#[export] Hint Resolve natpmswap4 : nat.

Proposition n_leq_m_n_leq_plus_m_k (n m k : nat)
  : n <= m -> n <= m + k.
Proof.
  intro l; apply (leq_trans l); exact (n_leq_add_n_k m k).
Defined.

Proposition nat_add_bifunctor (n n' m m' : nat)
  : n <= m -> n' <= m' -> n + n' <= m + m'.
Proof.
  revert n' m m'; simple_induction n n IHn.
  - intros n' m m' l l'. simpl.
    apply (leq_trans l'). exact (n_leq_add_n_k' m' m).
  - intros n' m; destruct m.
    + intros. contradiction (not_leq_Sn_0 n).
    + intros m' l l'. apply leq_S_n in l. simpl.
      apply leq_S_n', IHn.
      * exact l.
      * exact l'.
Defined.

#[export] Hint Resolve nat_add_bifunctor : nat.
#[export] Hint Resolve nataddpreserveslt : nat.
#[export] Hint Resolve nataddpreservesleq' : nat.
#[export] Hint Resolve nataddpreserveslt' : nat.
#[export] Hint Resolve natineq0eq0 : nat.
#[export] Hint Resolve n_leq_add_n_k : nat.
#[export] Hint Resolve n_leq_m_n_leq_plus_m_k : nat.

#[export] Hint Immediate add_n_sub_n_eq : nat.
#[export] Hint Immediate add_n_sub_n_eq' : nat.

#[export] Hint Rewrite <- add_n_O : nat.
#[export] Hint Rewrite -> add_O_n : nat.
#[export] Hint Rewrite -> add_n_sub_n_eq : nat.
#[export] Hint Rewrite -> add_n_sub_n_eq' : nat.
#[export] Hint Rewrite -> nataddsub_assoc : nat.

Ltac autorewrite_or_fail := progress ltac:(autorewrite with nat).

#[export] Hint Extern 7 => autorewrite_or_fail : nat.

Proposition strong_induction (P : nat -> Type)
  : (forall n : nat, (forall m : nat,  (m < n) -> P m) -> P n) ->
  forall n : nat, P n.
Proof.
  intro a.
  assert (forall n m: nat, m < n -> P m) as X. {
    simple_induction n n IHn.
    - intros m l. contradiction (not_lt_n_0 m).
    - intros m l. apply leq_S_n in l.
      destruct l as [ | n].
      + apply a; intros ? ?; now apply IHn.
      + now apply (IHn m), leq_S_n'.
  }
  intro n. apply (X (n.+1) n), (leq_n n.+1).
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
  - destruct (symmetric_paths _ _ (sub_n_0 n)); constructor.
  - destruct (@leq_dichot n k) as [l | g].
    + destruct (symmetric_paths _ _ (sub_leq_0 _ _ _)) in IHk.
      apply leq_S in l.
      destruct (symmetric_paths _ _ (sub_leq_0 _ _ _)). exact IHk.
    + change k.+1 with (1 + k). destruct (nat_add_comm k 1).
      destruct (symmetric_paths _ _ (subsubadd n k 1)).
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
  - contradiction (not_lt_n_0 k).
  - change (n.+1 - k.+1) with (n - k). apply leq_S_n in ineq.
    apply (nataddsub_assoc_lemma _).
Defined.
  
Lemma ineq_sub (n m : nat) : n <= m -> m - (m - n) = n.
Proof.
  revert m; simple_induction n n IHn.
  - intros. destruct (symmetric_paths _ _ (sub_n_0 m)),
      (symmetric_paths _ _ (sub_n_n m));
      reflexivity.
  - intros m ineq. change (m - n.+1) with (m - (1 + n)).
    (destruct (nat_add_comm n 1)).
    destruct (symmetric_paths _ _ (subsubadd m n 1)). 
    destruct (S_predn (m - n) 0 (lt_sub_gt_0 _ _ ineq)); simpl;
      destruct (symmetric_paths _ _ (sub_n_0 (pred (m - n)))).
    assert (0 < m - n) as dp by exact (lt_sub_gt_0 _ _ ineq).
    assert (pred (m - n) < m) as sh by
        ( unfold "<";
          destruct (symmetric_paths _ _ (S_predn _ 0 _));
          exact sub_less).
    destruct (symmetric_paths _ _ (ineq_sub' _ _ _)).
    destruct (symmetric_paths _ _ (S_predn _ 0 _)).
    apply (ap S), IHn, leq_S', ineq.
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
    + exact (leq_S' _ _ _).
Defined.

(** This tautology accepts a (potentially opaqued or QED'ed) proof of [n <= m], and returns a transparent proof which can be computed with (i.e., one can loop from n to m) *) 
Definition leq_wrapper {n m : nat} : n <= m -> n <= m.
Proof.
  intro ineq.
  destruct (@leq_dichot n m) as [l | g].
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
