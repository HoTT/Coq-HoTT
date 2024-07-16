Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Basics.Trunc Basics.Equivalences Basics.Nat Basics.Classes.
Export Basics.Nat.

Local Set Universe Minimization ToSet.
Local Unset Elimination Schemes.

(** * Natural Numbers *)

(** We want to close the trunc_scope so that notations from there don't conflict here. *)
Local Close Scope trunc_scope.
Local Open Scope nat_scope.

(** TODO: Some results are prefixed with [nat_] and some are not.  Should we be more consistent? *)

(** ** Basic operations on naturals *)

(** *** Iteration *)

(** [n]th iteration of the function [f : A -> A].  We have definitional equalities [nat_iter 0 f x = x] and [nat_iter n.+1 f x = f (nat_iter n f x)].  We make this a notation, so it doesn't add a universe variable for the universe containing [A]. *)
Notation nat_iter n f x
  := ((fix F (m : nat)
      := match m with
        | 0 => x
        | m'.+1 => f (F m')
        end) n).

(** *** Successor and Predecessor *)

(** [nat_succ n] is the successor of a natural number [n]. *)
Notation nat_succ := S (only parsing).

(** [nat_pred n] is the predecessor of a natural number [n]. When [n] is [0] we return [0]. *)
Definition nat_pred n : nat :=
  match n with
  | 0 => n
  | S n' => n'
  end.

(** *** Arithmetic Operations *)

(** Addition of natural numbers *)
Definition nat_add n m : nat
  := nat_iter n nat_succ m.

Notation "n + m" := (nat_add n m) : nat_scope.

(** Multiplication of natural numbers *)
Definition nat_mul n m : nat
  := nat_iter n (nat_add m) 0.

Notation "n * m" := (nat_mul n m) : nat_scope.

(** Truncated subtraction: [n - m] is [0] if [n <= m] *)
Fixpoint nat_sub n m : nat :=
  match n, m with
  | S n' , S m' => nat_sub n' m'
  | _ , _ => n
  end.

Notation "n - m" := (nat_sub n m) : nat_scope.

(** Exponentiation of natural numbers. *)
Definition nat_pow n m :=
  nat_iter m (nat_mul n) 1.

(** TODO: merge witth nat_pow (order of arguments needs adjusting). *)
(** Exponentiation *)
Fixpoint nat_exp (n m : nat) : nat
  := match m with
       | 0 => 1
       | S m => nat_exp n m * n
     end.

(** *** Maximum and Minimum *)

(** The maximum [nat_max n m] of two natural numbers [n] and [m]. *) 
Fixpoint nat_max n m :=
  match n, m with
  | 0 , _ => m
  | S n' , 0 => n'.+1
  | S n' , S m' => (nat_max n' m').+1
  end.

(** The minimum [nat_min n m] of two natural numbers [n] and [m]. *)
Fixpoint nat_min n m :=
  match n, m with
  | 0 , _ => 0
  | S n' , 0 => 0
  | S n' , S m' => S (nat_min n' m')
  end.

(** *** Euclidean division *)

(** This division is linear and tail-recursive. In [divmod], [y] is the predecessor of the actual divisor, and [u] is [y] sub the real remainder. *)

Fixpoint divmod x y q u : nat * nat :=
  match x with
  | 0 => (q , u)
  | S x' =>
    match u with
    | 0 => divmod x' y (S q) y
    | S u' => divmod x' y q u'
    end
  end.

Definition div x y : nat :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.

Definition modulo x y : nat :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "/" := div : nat_scope.
Infix "mod" := modulo : nat_scope.

(** *** Greatest common divisor *)

(** We use Euclid algorithm, which is normally not structural, but Coq is now clever enough to accept this (behind modulo there is a subtraction, which now preserves being a subterm) *)

Fixpoint gcd a b :=
  match a with
  | O => b
  | S a' => gcd (b mod a'.+1) a'.+1
  end.

(** *** Factorial *)

Fixpoint factorial (n : nat) : nat
  := match n with
       | 0 => 1
       | S n => S n * factorial n
     end.

(** ** Properties of [nat_iter]. *)

Lemma nat_iter_succ_r n {A} (f : A -> A) (x : A)
  : nat_iter (S n) f x = nat_iter n f (f x).
Proof.
  simple_induction n n IHn; simpl; trivial.
  exact (ap f IHn).
Defined.

Theorem nat_iter_add (n m : nat) {A} (f : A -> A) (x : A)
  : nat_iter (n + m) f x = nat_iter n f (nat_iter m f x).
Proof.
  simple_induction n n IHn; simpl; trivial.
  exact (ap f IHn).
Defined.

(** Preservation of invariants : if [f : A -> A] preserves the invariant [P], then the iterates of [f] also preserve it. *)
Theorem nat_iter_invariant (n : nat) {A} (f : A -> A) (P : A -> Type)
  : (forall x, P x -> P (f x)) -> forall x, P x -> P (nat_iter n f x).
Proof.
  simple_induction n n IHn; simpl; trivial.
  intros Hf x Hx.
  apply Hf, IHn; trivial.
Defined.

(** ** Properties of Successors *)

(** TODO: remove these *)
Local Definition ap_S := @ap _ _ S.
Local Definition ap_nat := @ap nat.
#[export] Hint Resolve ap_S : core.
#[export] Hint Resolve ap_nat : core.

Definition nat_pred_succ@{} n : nat_pred (nat_succ n) = n
  := idpath.

(** Injectivity of successor *)
Definition path_nat_S@{} n m (H : S n = S m) : n = m := ap nat_pred H.
#[export] Hint Immediate path_nat_S : core.

(** TODO: rename to [neq_S] *)
(** TODO: avoid auto in proof. *)
Definition not_eq_S@{} n m : n <> m -> S n <> S m.
Proof.
  auto.
Defined.
#[export] Hint Resolve not_eq_S : core.

(** TODO: rename to [neq_O_S] *)
(** Zero is not the successor of a number *)
Definition not_eq_O_S@{} : forall n, 0 <> S n.
Proof.
  discriminate.
Defined.
#[export] Hint Resolve not_eq_O_S : core.

(** TODO: rename to [neq_n_Sn] *)
(** TODO: prove above using this *)
(** TODO: remove auto. *)
Theorem not_eq_n_Sn@{} n : n <> S n.
Proof.
  simple_induction' n; auto.
Defined.
#[export] Hint Resolve not_eq_n_Sn : core.

(** *** Properties of Addition *)

(** [0] is the left identity of addition. *)
Definition nat_add_zero_l@{} n : 0 + n = n
  := idpath.

(** [0] is the right identity of addition. *)
Definition nat_add_zero_r@{} n : n + 0 = n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - apply (ap nat_succ).
    exact IHn.
Defined.
#[export] Hint Resolve nat_add_zero_r : core.

(** Adding a successor on the left is the same as adding and then taking the successor. *)
Definition nat_add_succ_l@{} n m : n.+1 + m = (n + m).+1
  := idpath.

(** Adding a successor on the right is the same as adding and then taking the successor. *)
Definition nat_add_succ_r@{} n m : n + m.+1 = (n + m).+1.
Proof.
  simple_induction' n; simpl; auto.
Defined.
#[export] Hint Resolve nat_add_succ_r: core.

(** Addition of natural numbers is commutative. *)
Definition nat_add_comm@{} n m : n + m = m + n.
Proof.
  induction n.
  - exact (nat_add_zero_r m)^.
  - rhs nrapply nat_add_succ_r.
    apply (ap nat_succ).
    exact IHn.
Defined.

(** Addition of natural numbers is associative. *)
Definition nat_add_assoc@{} n m k : n + (m + k) = (n + m) + k.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - nrapply (ap nat_succ).
    exact IHn.
Defined.

(** *** Properties of Multiplication *)

(** Multiplication by [0] on the left is [0]. *)
Definition nat_mul_zero_l@{} n : 0 * n = 0
  := idpath.

(** Multiplicaiton by [0] on the right is [0]. *)
Definition nat_mul_zero_r@{} n : n * 0 = 0.
Proof.
  by induction n.
Defined.
#[export] Hint Resolve nat_mul_zero_r : core.

Definition nat_mul_succ_l@{} n m : n.+1 * m = m + n * m
  := idpath.

Definition nat_mul_succ_r@{} n m : n * m.+1 = n * m + n.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - rhs nrapply nat_add_succ_r.
    nrapply (ap nat_succ).
    rhs_V nrapply nat_add_assoc.
    nrapply (ap (nat_add m)).
    exact IHn.
Defined.
#[export] Hint Resolve nat_mul_succ_r : core.

(** Multiplication of natural numbers is commutative. *)
Definition nat_mul_comm@{} n m : n * m = m * n.
Proof.
  induction m as [|m IHm]; simpl.
  - nrapply nat_mul_zero_r.
  - lhs nrapply nat_mul_succ_r.
    lhs nrapply nat_add_comm.
    snrapply (ap (nat_add n)).
    exact IHm.
Defined.

(** Multiplication of natural numbers distributes over addition on the left. *)
Definition nat_dist_l@{} n m k : n * (m + k) = n * m + n * k.
Proof.
  induction n as [|n IHn]; simpl.
  - reflexivity.
  - lhs_V nrapply nat_add_assoc.
    rhs_V nrapply nat_add_assoc.
    nrapply (ap (nat_add m)).
    lhs nrapply nat_add_comm.
    rewrite IHn.
    lhs_V nrapply nat_add_assoc.
    nrapply (ap (nat_add (n * m))).
    nrapply nat_add_comm.
Defined.

(** Multiplication of natural numbers distributes over addition on the right. *)
Definition nat_dist_r@{} n m k : (n + m) * k = n * k + m * k.
Proof.
  rewrite 3 (nat_mul_comm _ k).
  nrapply nat_dist_l.
Defined.

(** ** Equality of natural numbers *)

(** *** Boolean equality and its properties *)

(** [nat] has decidable paths *)
Global Instance decidable_paths_nat@{} : DecidablePaths nat.
Proof.
  intros n; simple_induction n n IHn;
  intros m; destruct m.
  - exact (inl idpath).
  - exact (inr (not_eq_O_S m)).
  - exact (inr (fun p => not_eq_O_S n p^)).
  - destruct (IHn m) as [p|q].
    + exact (inl (ap S p)).
    + exact (inr (fun p => q (path_nat_S _ _ p))).
Defined.

(** And is therefore a HSet *)
Global Instance hset_nat : IsHSet nat := _.

(** ** Inequality of natural numbers *)

Cumulative Inductive leq (n : nat) : nat -> Type0 :=
| leq_n : leq n n
| leq_S : forall m, leq n m -> leq n (S m).

Scheme leq_ind := Induction for leq Sort Type.
Scheme leq_rect := Induction for leq Sort Type.
Scheme leq_rec := Minimality for leq Sort Type.

Notation "n <= m" := (leq n m) : nat_scope.
#[export] Hint Constructors leq : core.

Existing Class leq.
Global Existing Instances leq_n leq_S.

Notation leq_refl := leq_n (only parsing).
Global Instance reflexive_leq : Reflexive leq := leq_n.

Lemma leq_trans {x y z} : x <= y -> y <= z -> x <= z.
Proof.
  induction 2; auto.
Defined.

Global Instance transitive_leq : Transitive leq := @leq_trans.

Lemma leq_n_pred n m : leq n m -> leq (nat_pred n) (nat_pred m).
Proof.
  induction 1; auto.
  destruct m; simpl; auto.
Defined.

Lemma leq_S_n : forall n m, n.+1 <= m.+1 -> n <= m.
Proof.
  intros n m.
  apply leq_n_pred.
Defined.

Lemma leq_S_n' n m : n <= m -> n.+1 <= m.+1.
Proof.
  induction 1; auto.
Defined.
Global Existing Instance leq_S_n' | 100.

Lemma not_leq_Sn_n n : ~ (n.+1 <= n).
Proof.
  simple_induction n n IHn.
  { intro p.
    inversion p. }
  intros p.
  by apply IHn, leq_S_n.
Defined.

(** A general form for injectivity of this constructor *)
Definition leq_n_inj_gen n k (p : n <= k) (r : n = k) : p = r # leq_n n.
Proof.
  destruct p.
  + assert (c : idpath = r) by apply path_ishprop.
    destruct c.
    reflexivity.
  + destruct r^.
    contradiction (not_leq_Sn_n _ p).
Defined.

(** Which we specialise to this lemma *)
Definition leq_n_inj n (p : n <= n) : p = leq_n n
  := leq_n_inj_gen n n p idpath.

Fixpoint leq_S_inj_gen n m k (p : n <= k) (q : n <= m) (r : m.+1 = k)
  : p = r # leq_S n m q.
Proof.
  revert m q r.
  destruct p.
  + intros k p r.
    destruct r.
    contradiction (not_leq_Sn_n _ p).
  + intros m' q r.
    pose (r' := path_nat_S _ _ r).
    destruct r'.
    assert (t : idpath = r) by apply path_ishprop.
    destruct t.
    cbn. apply ap.
    destruct q.
    1:  apply leq_n_inj.
    apply (leq_S_inj_gen n m _ p q idpath).
Defined.

Definition leq_S_inj n m (p : n <= m.+1) (q : n <= m) : p = leq_S n m q
  := leq_S_inj_gen n m m.+1 p q idpath.

Global Instance ishprop_leq n m : IsHProp (n <= m).
Proof.
  apply hprop_allpath.
  intros p q; revert p.
  induction q.
  + intros y.
    rapply leq_n_inj.
  + intros y.
    rapply leq_S_inj.
Defined.

Global Instance leq_0_n n : 0 <= n | 10.
Proof.
  simple_induction' n; auto.
Defined.

Lemma not_leq_Sn_0 n : ~ (n.+1 <= 0).
Proof.
  intros p.
  apply (fun x => leq_trans x (leq_0_n n)) in p.
  contradiction (not_leq_Sn_n _ p).
Defined.

Definition equiv_leq_S_n n m : n.+1 <= m.+1 <~> n <= m.
Proof.
  srapply equiv_iff_hprop.
  apply leq_S_n.
Defined.

Global Instance decidable_leq n m : Decidable (n <= m).
Proof.
  revert n.
  simple_induction' m; intros n.
  - destruct n.
    + left; exact _.
    + right; apply not_leq_Sn_0.
  - destruct n.
    + left; exact _.
    + rapply decidable_equiv'.
      symmetry.
      apply equiv_leq_S_n.
Defined.

Fixpoint leq_add n m : n <= (m + n).
Proof.
  destruct m.
  1: apply leq_n.
  apply leq_S, leq_add.
Defined.

(** We define the less-than relation [lt] in terms of [leq] *)
Definition lt n m : Type0 := leq (S n) m.

(** We declare it as an existing class so typeclass search is performed on its goals. *)
Existing Class lt.
#[export] Hint Unfold lt : core typeclass_instances.
Infix "<" := lt : nat_scope.
(** We add a typeclass instance for unfolding the definition so lemmas about [leq] can be used. *)
Global Instance lt_is_leq n m : leq n.+1 m -> lt n m | 100 := idmap.

(** We should also give them their various typeclass instances *)
Global Instance transitive_lt : Transitive lt.
Proof.
  hnf; unfold lt in *.
  intros x y z p q.
  rapply leq_trans.
Defined.

Global Instance decidable_lt n m : Decidable (lt n m) := _.

Definition ge n m := leq m n.
Existing Class ge.
#[export] Hint Unfold ge : core typeclass_instances.
Infix ">=" := ge : nat_scope.
Global Instance ge_is_leq n m : leq m n -> ge n m | 100 := idmap.

Global Instance reflexive_ge : Reflexive ge := leq_n.
Global Instance transitive_ge : Transitive ge := fun x y z p q => leq_trans q p.
Global Instance decidable_ge n m : Decidable (ge n m) := _.

Definition gt n m := lt m n.
Existing Class gt.
#[export] Hint Unfold gt : core typeclass_instances.
Infix ">" := gt : nat_scope.
Global Instance gt_is_leq n m : leq m.+1 n -> gt n m | 100 := idmap.

Global Instance transitive_gt : Transitive gt
  := fun x y z p q => transitive_lt _ _ _ q p.
Global Instance decidable_gt n m : Decidable (gt n m) := _.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z"  := (x <= y /\  y < z) : nat_scope.
Notation "x < y < z"   := (x < y  /\  y < z) : nat_scope.
Notation "x < y <= z"  := (x < y  /\ y <= z) : nat_scope.

(** Principle of double induction *)

Theorem nat_double_ind (R : nat -> nat -> Type)
  (H1 : forall n, R 0 n) (H2 : forall n, R (S n) 0)
  (H3 : forall n m, R n m -> R (S n) (S m))
  : forall n m:nat, R n m.
Proof.
  simple_induction' n; auto.
  destruct m; auto.
Defined.

(** Maximum and minimum : definitions and specifications *)

Lemma nat_max_n_n n : nat_max n n = n.
Proof.
  simple_induction' n; cbn; auto.
Defined.
#[export] Hint Resolve nat_max_n_n : core.

Lemma nat_max_Sn_n n : nat_max (S n) n = S n.
Proof.
  simple_induction' n; cbn; auto.
Defined.
#[export] Hint Resolve nat_max_Sn_n : core.

Lemma nat_max_comm n m : nat_max n m = nat_max m n.
Proof.
  revert m; simple_induction' n; destruct m; cbn; auto.
Defined.

Lemma nat_max_0_n n : nat_max 0 n = n.
Proof.
  auto.
Defined.
#[export] Hint Resolve nat_max_0_n : core.

Lemma nat_max_n_0 n : nat_max n 0 = n.
Proof.
  by rewrite nat_max_comm.
Defined.
#[export] Hint Resolve nat_max_n_0 : core.

Theorem nat_max_l : forall n m, m <= n -> nat_max n m = n.
Proof.
  intros n m; revert n; simple_induction m m IHm; auto.
  intros [] p.
  1: inversion p.
  cbn; by apply (ap S), IHm, leq_S_n.
Defined.

Theorem nat_max_r : forall n m : nat, n <= m -> nat_max n m = m.
Proof.
  intros; rewrite nat_max_comm; by apply nat_max_l.
Defined.

Lemma nat_min_comm : forall n m, nat_min n m = nat_min m n.
Proof.
  simple_induction' n; destruct m; cbn; auto.
Defined.

Theorem nat_min_l : forall n m : nat, n <= m -> nat_min n m = n.
Proof.
  simple_induction n n IHn; auto.
  intros [] p.
  1: inversion p.
  cbn; by apply (ap S), IHn, leq_S_n.
Defined.

Theorem nat_min_r : forall n m : nat, m <= n -> nat_min n m = m.
Proof.
  intros; rewrite nat_min_comm; by apply nat_min_l.
Defined.

(** ** Arithmetic *)

Global Instance isinj_S : IsInjective S.
Proof.
  intros x y p.
  by apply path_nat_S.
Defined.

Global Instance isinj_nat_add_l@{} k : IsInjective (nat_add k).
Proof.
  simple_induction k k Ik; exact _.
Defined.

Definition isinj_nat_add_r@{} k : IsInjective (fun x =>nat_add x k).
Proof.
  intros x y H.
  rewrite 2 (nat_add_comm _ k) in H.
  exact (isinj_nat_add_l k _ _ H).
Defined.

(** ** Natural number ordering *)

(** ** Theorems about natural number ordering *)

Lemma leq_antisym {x y} : x <= y -> y <= x -> x = y.
Proof.
  intros p q.
  destruct p.
  1: reflexivity.
  destruct x; [inversion q|].
  apply leq_S_n in q.
  pose (r := leq_trans p q).
  by apply not_leq_Sn_n in r.
Defined.

Definition not_lt_n_n n : ~ (n < n) := not_leq_Sn_n n.

Definition leq_1_Sn {n} : 1 <= n.+1 := leq_S_n' 0 n (leq_0_n _).

Fixpoint leq_dichot {m} {n} : (m <= n) + (m > n).
Proof.
  simple_induction' m; simple_induction' n.
  - left; reflexivity.
  - left; apply leq_0_n.
  - right; unfold lt; apply leq_1_Sn.
  - assert ((m <= n) + (n < m)) as X by apply leq_dichot.
    destruct X as [leqmn|ltnm].
    + left; apply leq_S_n'; assumption.
    + right; apply leq_S_n'; assumption.
Defined.

Lemma not_lt_n_0 n : ~ (n < 0).
Proof.
  apply not_leq_Sn_0.
Defined.

(** ** Arithmetic relations between [trunc_index] and [nat]. *)

Lemma trunc_index_add_nat_add (n : nat)
  : trunc_index_add n n = n.+1 + n.+1.
Proof.
  induction n as [|n IH]; only 1: reflexivity.
  refine (trunc_index_add_succ _ _ @ _).
  refine (ap trunc_S _ @ _).
  { refine (trunc_index_add_comm _ _ @ _).
    refine (trunc_index_add_succ _ _ @ _).
    exact (ap trunc_S IH). }
  refine (_ @ ap nat_to_trunc_index _).
  2: exact (nat_add_succ_r _ _)^.
  reflexivity.
Defined.
