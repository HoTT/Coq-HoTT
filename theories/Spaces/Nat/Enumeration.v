(** * Enumerations by the natural numbers *)

(** We show that a type with decidable equality is equivalent to the natural numbers when it is the image of a function [s] from the natural numbers such that, for every [n], some element is not among the values of [s] up to [n].  Along the way we show that an unbounded decidable subset of the natural numbers is equivalent to the natural numbers, and we enumerate pairs of natural numbers. *)

From HoTT Require Import Basics Types.Sigma Types.Prod Truncations.Core Spaces.Nat.Core Misc.BoundedSearch.

Local Open Scope nat_scope.

Section subset.
  Context (P : nat -> Type) `{forall n, Decidable (P n)} `{forall n, IsHProp (P n)}.

  (** The number of elements of [P] below [n]. *)
  Fixpoint subset_count (n : nat) : nat
    := match n with
       | 0 => 0
       | S n => if dec (P n) then S (subset_count n) else subset_count n
       end.

  Local Notation count := subset_count.

  Lemma subset_count_succ_in (n : nat) : P n -> count (S n) = S (count n).
  Proof.
    intros p; cbn; destruct (dec (P n)) as [_|np]; [reflexivity|destruct (np p)].
  Qed.

  Lemma subset_count_succ_notin (n : nat) : ~ P n -> count (S n) = count n.
  Proof.
    intros np; cbn; destruct (dec (P n)) as [p|_]; [destruct (np p)|reflexivity].
  Qed.

  Lemma subset_count_succ_leq (n : nat) : count n <= count (S n).
  Proof.
    cbn; destruct (dec (P n)); [exact _|reflexivity].
  Qed.

  Lemma subset_count_leq (n m : nat) : n <= m -> count n <= count m.
  Proof.
    intros l; induction l as [|m l IH].
    - reflexivity.
    - exact (leq_trans IH (subset_count_succ_leq m)).
  Qed.

  Lemma subset_count_lt (n m : nat) : P n -> n < m -> count n < count m.
  Proof.
    intros p l; unfold lt.
    rewrite <- (subset_count_succ_in n p).
    exact (subset_count_leq _ _ l).
  Qed.

  Lemma subset_count_inj (n m : nat) : P n -> P m -> count n = count m -> n = m.
  Proof.
    intros p q e.
    destruct (nat_trichotomy n m) as [[l|e']|l].
    - destruct (lt_irrefl _ (transport (fun k => k < count m) e (subset_count_lt n m p l))).
    - exact e'.
    - destruct (lt_irrefl _ (transport (fun k => count m < k) e (subset_count_lt m n q l))).
  Qed.

  (** If [P] is unbounded, then [count] is unbounded. *)
  Context (unbounded : forall n, {m : nat & prod (n <= m) (P m)}).

  Lemma subset_count_unbounded (k : nat) : {n : nat & k < count n}.
  Proof.
    induction k as [|k [n l]].
    - destruct (unbounded 0) as [m [_ p]]; exists (S m).
      rewrite (subset_count_succ_in m p); exact _.
    - destruct (unbounded n) as [m [nm p]]; exists (S m).
      rewrite (subset_count_succ_in m p).
      exact (leq_succ (leq_trans l (subset_count_leq _ _ nm))).
  Qed.

  (** Every number is the count of an element of [P]. *)
  Lemma subset_count_hit (n k : nat) : k < count n -> {m : nat & prod (P m) (count m = k)}.
  Proof.
    induction n as [|n IH]; intros l.
    - destruct (not_lt_zero_r _ l).
    - destruct (dec (k < count n)) as [l'|nl]; [exact (IH l')|].
      destruct (dec (P n)) as [p|np].
      + exists n; split; [exact p|].
        rewrite (subset_count_succ_in n p) in l.
        exact (leq_antisym (fst geq_iff_not_lt nl) (equiv_leq_succ _ _ l)).
      + rewrite (subset_count_succ_notin n np) in l; destruct (nl l).
  Qed.

  (** An unbounded decidable subset of the natural numbers is equivalent to the natural numbers, by counting. *)
  Definition equiv_nat_unbounded_subset : nat <~> {m : nat & P m}.
  Proof.
    symmetry.
    srapply (equiv_adjointify (fun m => count m.1)).
    - intros k.
      destruct (subset_count_unbounded k) as [n l].
      destruct (subset_count_hit n k l) as [m [p _]].
      exact (m; p).
    - intros k; cbn.
      destruct (subset_count_unbounded k) as [n l].
      exact (snd (subset_count_hit n k l).2).
    - intros [m p]; apply path_sigma_hprop; cbn.
      destruct (subset_count_unbounded (count m)) as [n l].
      destruct (subset_count_hit n (count m) l) as [m' [p' e]]; cbn.
      exact (subset_count_inj m' m p' p e).
  Defined.
End subset.

(** A type with decidable equality that is the image of the natural numbers, and is not covered by any initial segment of them, is equivalent to the natural numbers. *)
Definition equiv_nat_enumeration {X : Type} `{DecidablePaths X} (s : nat -> X)
  (surj : forall x, hexists (fun n => s n = x))
  (avoid : forall n, {x : X & forall m, m <= n -> s m <> x})
  : nat <~> X.
Proof.
  (** The least index of each element. *)
  pose (index x := (minimal_n (fun n => s n = x) _ (surj x)).1).
  assert (s_index : forall x, s (index x) = x)
    by (intros x; exact (minimal_n (fun n => s n = x) _ (surj x)).2).
  pose (D n := index (s n) = n).
  refine (_ oE equiv_nat_unbounded_subset D _).
  - srapply (equiv_adjointify (fun n => s n.1) (fun x => (index x; ap index (s_index x)))).
    + exact s_index.
    + intros [n d]; apply path_sigma_hprop; exact d.
  - intros n.
    destruct (avoid n) as [x ne].
    exists (index x); split.
    + apply geq_iff_not_lt; intros l.
      exact (ne (index x) (leq_lt l) (s_index x)).
    + exact (ap index (s_index x)).
Defined.

(** ** Enumerating pairs *)

(** We enumerate pairs of natural numbers diagonal by diagonal. *)
Fixpoint nat_unpair (n : nat) : nat * nat
  := match n with
     | 0 => (0, 0)
     | S n => match nat_unpair n with
             | (0, b) => (S b, 0)
             | (S a, b) => (a, S b)
             end
     end.

Lemma nat_unpair_hit (a b : nat) : {n : nat & nat_unpair n = (a, b)}.
Proof.
  (** By induction on the diagonal [a + b], and then on [b]. *)
  pose (d := a + b); assert (e : a + b = d) by reflexivity; clearbody d.
  revert a b e; induction d as [|d IH]; intros a b; revert a.
  - intros a e; exists 0.
    destruct a; [|discriminate e]; destruct b; [|discriminate e]; reflexivity.
  - induction b as [|b IHb]; intros a e.
    + destruct (IH 0 d idpath) as [n p]; exists (S n); cbn; rewrite p.
      rewrite <- e, nat_add_zero_r; reflexivity.
    + destruct (IHb (S a) (nat_add_succ_l a b @ (nat_add_succ_r a b)^ @ e)) as [n p].
      exists (S n); cbn; rewrite p; reflexivity.
Defined.

(** Finitely many natural numbers have a strict upper bound. *)
Lemma nat_bound (g : nat -> nat) (n : nat) : {k : nat & forall m, m <= n -> g m < k}.
Proof.
  induction n as [|n [k IH]].
  - exists (S (g 0)); intros m l.
    rewrite (path_zero_leq_zero_r m l); exact _.
  - exists (k + S (g (S n))); intros m l.
    destruct (leq_succ_dichotomy l) as [p|l'].
    + rewrite p; exact (leq_add_l _ _).
    + exact (leq_trans (IH m l') (leq_add_r _ _)).
Defined.

(** A product of a type equivalent to the natural numbers and an image of the natural numbers, both with decidable equality, is equivalent to the natural numbers. *)
Definition equiv_nat_prod_enumeration {X Y : Type} `{DecidablePaths X} `{DecidablePaths Y}
  (e : nat <~> X) (s : nat -> Y) (surj : forall y, hexists (fun n => s n = y))
  : nat <~> X * Y.
Proof.
  pose (s' n := (e (fst (nat_unpair n)), s (snd (nat_unpair n)))).
  apply (equiv_nat_enumeration s').
  - intros [x y]; specialize (surj y); strip_truncations; apply tr.
    destruct surj as [b p].
    destruct (nat_unpair_hit (e^-1 x) b) as [n q]; exists n.
    unfold s'; rewrite q; cbn; rewrite eisretr, p; reflexivity.
  - intros n.
    destruct (nat_bound (fun m => e^-1 (fst (s' m))) n) as [k l].
    exists (e k, s 0); intros m lm p.
    pose proof (l m lm) as q; cbv beta in q.
    rewrite p in q; cbn in q; rewrite eissect in q.
    exact (lt_irrefl _ q).
Defined.
