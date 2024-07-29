Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Basics.Trunc Basics.Equivalences Basics.Nat Basics.Classes.
Export Basics.Nat.

Local Set Universe Minimization ToSet.
Local Unset Elimination Schemes.

(** * Natural numbers *)

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

(** *** Successor and predecessor *)

(** [nat_succ n] is the successor of a natural number [n]. We defined a notation [x.+1] for it in Overture.v. *)
Notation nat_succ := S (only parsing).

(** [nat_pred n] is the predecessor of a natural number [n]. When [n] is [0] we return [0]. *)
Definition nat_pred n : nat :=
  match n with
  | 0 => n
  | S n' => n'
  end.

(** *** Arithmetic operations *)

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

(** Powers or exponentiation of natural numbers. *)
Definition nat_pow n m := nat_iter m (nat_mul n) 1.

(** *** Maximum and minimum *)

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

(** ** Comparison Predicates *)

(** *** Less Than or Equal To *)

Inductive leq (n : nat) : nat -> Type0 :=
| leq_refl : leq n n
| leq_succ_r m : leq n m -> leq n (S m).

Arguments leq_succ_r {n m} _.

Scheme leq_ind := Induction for leq Sort Type.
Scheme leq_rect := Induction for leq Sort Type.
Scheme leq_rec := Induction for leq Sort Type.

Notation "n <= m" := (leq n m) : nat_scope.

Existing Class leq.
Global Existing Instances leq_refl leq_succ_r.

(** *** Less Than *)

(** We define the less-than relation [lt] in terms of [leq] *)
Definition lt n m : Type0 := leq (S n) m.

(** We declare it as an existing class so typeclass search is performed on its goals. *)
Existing Class lt.
#[export] Hint Unfold lt : typeclass_instances.
Infix "<" := lt : nat_scope.
Global Instance lt_is_leq n m : leq n.+1 m -> lt n m | 100 := idmap.

(** *** Greater Than or Equal To *)

Definition geq n m := leq m n.
Existing Class geq.
#[export] Hint Unfold geq : typeclass_instances.
Infix ">=" := geq : nat_scope.
Global Instance geq_is_leq n m : leq m n -> geq n m | 100 := idmap.

(*** Greater Than *)

Definition gt n m := lt m n.
Existing Class gt.
#[export] Hint Unfold gt : typeclass_instances.
Infix ">" := gt : nat_scope.
Global Instance gt_is_leq n m : leq m.+1 n -> gt n m | 100 := idmap.

(** *** Combined Comparison Predicates *)

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : nat_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : nat_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : nat_scope.

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

(** ** Properties of successors *)

Definition nat_pred_succ@{} n : nat_pred (nat_succ n) = n
  := idpath.

(** Injectivity of successor. *)
Definition path_nat_succ@{} n m (H : S n = S m) : n = m := ap nat_pred H.
Global Instance isinj_succ : IsInjective nat_succ := path_nat_succ.

(** Inequality of sucessors is implied with inequality of the arguments. *)
Definition neq_nat_succ@{} n m : n <> m -> S n <> S m.
Proof.
  intros np q.
  apply np.
  exact (path_nat_succ _ _ q).
Defined.

(** Zero is not the successor of a number. *)
Definition neq_nat_zero_succ@{} n : 0 <> S n.
Proof.
  discriminate.
Defined.

(** A natural number cannot be equal to its own successor. *)
Theorem neq_nat_succ'@{} n : n <> S n.
Proof.
  simple_induction' n.
  - apply neq_nat_zero_succ.
  - by apply neq_nat_succ.
Defined.

(** ** Truncatedness of natural numbers *)

(** [nat] has decidable paths. *)
Global Instance decidable_paths_nat@{} : DecidablePaths nat.
Proof.
  intros n; simple_induction n n IHn;
  intros m; destruct m.
  - exact (inl idpath).
  - exact (inr (neq_nat_zero_succ m)).
  - exact (inr (fun p => neq_nat_zero_succ n p^)).
  - destruct (IHn m) as [p|q].
    + exact (inl (ap S p)).
    + exact (inr (fun p => q (path_nat_succ _ _ p))).
Defined.

(** [nat] is therefore a hset. *)
Global Instance ishset_nat : IsHSet nat := _.

(** ** Properties of addition *)

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

(** Adding a successor on the left is the same as adding and then taking the successor. *)
Definition nat_add_succ_l@{} n m : n.+1 + m = (n + m).+1
  := idpath.

(** Adding a successor on the right is the same as adding and then taking the successor. *)
Definition nat_add_succ_r@{} n m : n + m.+1 = (n + m).+1.
Proof.
  simple_induction' n; simpl.
  1: reflexivity.
  exact (ap S IH).
Defined.

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

(** Addition on the left is injective. *)
Global Instance isinj_nat_add_l@{} k : IsInjective (nat_add k).
Proof.
  simple_induction k k Ik; exact _.
Defined.

(** Addition on the right is injective. *)
Definition isinj_nat_add_r@{} k : IsInjective (fun x => nat_add x k).
Proof.
  intros x y H.
  nrapply (isinj_nat_add_l k).
  lhs nrapply nat_add_comm.
  lhs nrapply H.
  nrapply nat_add_comm.
Defined.

(** ** Properties of multiplication *)

(** Multiplication by [0] on the left is [0]. *)
Definition nat_mul_zero_l@{} n : 0 * n = 0
  := idpath.

(** Multiplicaiton by [0] on the right is [0]. *)
Definition nat_mul_zero_r@{} n : n * 0 = 0.
Proof.
  by induction n.
Defined.

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
  lhs nrapply nat_mul_comm.
  lhs nrapply nat_dist_l.
  nrapply ap011; nrapply nat_mul_comm.
Defined.

(** Multiplication of natural numbers is associative. *)
Definition nat_mul_assoc@{} n m k : n * (m * k) = n * m * k.
Proof.
  induction n as [|n IHn]; simpl.
  - reflexivity.
  - rhs nrapply nat_dist_r.
    nrapply (ap (nat_add (m * k))).
    exact IHn.
Defined.

(** Multiplication by [1] on the left is the identity. *)
Definition nat_mul_one_l@{} n : 1 * n = n
  := nat_add_zero_r _.
  
(** Multiplication by [1] on the right is the identity. *)
Definition nat_mul_one_r@{} n : n * 1 = n
  := nat_mul_comm _ _ @ nat_mul_one_l _.

(** ** Basic Properties of Comparison Predicates *)

(** *** Basic Properties of [leq] *)

(** [leq] is reflexive by definition. *)
Global Instance reflexive_leq : Reflexive leq := leq_refl.

(** Being less than or equal to is a transitive relation. *)
Definition leq_trans {x y z} : x <= y -> y <= z -> x <= z.
Proof.
  intros H1 H2; induction H2; exact _.
Defined.

(** [leq] is transtiive. *)
Global Instance transitive_leq : Transitive leq := @leq_trans.

(** [0] is less than or equal to any natural number. *)
Definition leq_zero n : 0 <= n.
Proof.
  simple_induction' n; exact _.
Defined.
Global Existing Instance leq_zero | 10.

(** A predecessor is less than or equal to a predecessor if the original number is less than or equal. *)
Definition leq_pred {n m} : leq n m -> leq (nat_pred n) (nat_pred m).
Proof.
  intros H; induction H.
  1: exact _.
  destruct m; exact _.
Defined.

(** A successor is less than or equal to a successor if the original numbers are less than or equal. *)
Definition leq_succ {n m} : n <= m -> n.+1 <= m.+1.
Proof.
  induction 1; exact _.
Defined.
Global Existing Instance leq_succ | 100.

(** The converse to [leq_succ] also holds. *)
Definition leq_succ' {n m} : n.+1 <= m.+1 -> n <= m := leq_pred.

(** TODO: rename *)
(** TODO: use lemmas about negating predicate *)
Lemma not_leq_Sn_n n : ~ (n.+1 <= n).
Proof.
  simple_induction n n IHn.
  { intro p.
    inversion p. }
  intros p.
  by apply IHn, leq_succ'.
Defined.

(** TODO: rename *)
Lemma not_leq_Sn_0 n : ~ (n.+1 <= 0).
Proof.
  intros p.
  apply (fun x => leq_trans x (leq_zero n)) in p.
  contradiction (not_leq_Sn_n _ p).
Defined.

(** A general form for injectivity of this constructor *)
Definition leq_refl_inj_gen n k (p : n <= k) (r : n = k) : p = r # leq_refl n.
Proof.
  destruct p.
  + assert (c : idpath = r) by apply path_ishprop.
    destruct c.
    reflexivity.
  + destruct r^.
    contradiction (not_leq_Sn_n _ p).
Defined.

(** Which we specialise to this lemma *)
Definition leq_refl_inj n (p : n <= n) : p = leq_refl n
  := leq_refl_inj_gen n n p idpath.

Fixpoint leq_succ_r_inj_gen n m k (p : n <= k) (q : n <= m) (r : m.+1 = k)
  : p = r # leq_succ_r q.
Proof.
  revert m q r.
  destruct p.
  + intros k p r.
    destruct r.
    contradiction (not_leq_Sn_n _ p).
  + intros m' q r.
    pose (r' := path_nat_succ _ _ r).
    destruct r'.
    assert (t : idpath = r) by apply path_ishprop.
    destruct t.
    cbn. apply ap.
    destruct q.
    1:  apply leq_refl_inj.
    apply (leq_succ_r_inj_gen n m _ p q idpath).
Defined.

Definition leq_succ_r_inj n m (p : n <= m.+1) (q : n <= m) : p = leq_succ_r q
  := leq_succ_r_inj_gen n m m.+1 p q idpath.

Global Instance ishprop_leq n m : IsHProp (n <= m).
Proof.
  apply hprop_allpath.
  intros p q; revert p.
  induction q.
  + intros y.
    rapply leq_refl_inj.
  + intros y.
    rapply leq_succ_r_inj.
Defined.

Definition equiv_leq_succ n m : n.+1 <= m.+1 <~> n <= m.
Proof.
  srapply equiv_iff_hprop.
  apply leq_succ'.
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
      apply equiv_leq_succ.
Defined.

(** [n.+1 <= m] implies [n <= m]. *)
Definition leq_succ_l {n m} : n.+1 <= m -> n <= m.
Proof.
  intro l; apply leq_succ'; exact _.
Defined.

(** *** Basic Properties of [lt] *)

(** [<=] and [<] imply [<] *)
Definition leq_lt_trans {n m k} : n <= m -> m < k -> n < k
  := fun leq lt => leq_trans (leq_succ leq) lt.

(** [<=] and [<] imply [<] *)
Definition lt_leq_trans {n m k} : n < m -> m <= k -> n < k
  := fun lt leq => leq_trans lt leq.

Definition leq_lt {n m} : n < m -> n <= m
  := leq_succ_l.

Definition lt_trans {n m k} : n < m -> m < k -> n < k
  := fun H1 H2 => leq_lt (leq_lt_trans H1 H2).

Global Instance transitive_lt : Transitive lt := @lt_trans.
Global Instance ishprop_lt n m : IsHProp (n < m) := _.
Global Instance decidable_lt n m : Decidable (lt n m) := _.

(** *** Basic Properties of [geq] *) 

Global Instance reflexive_geq : Reflexive geq := leq_refl.
Global Instance transitive_geq : Transitive geq := fun x y z p q => leq_trans q p.
Global Instance ishprop_geq n m : IsHProp (geq n m) := _.
Global Instance decidable_geq n m : Decidable (geq n m) := _.

(** *** Basic Properties of [gt] *)

Global Instance transitive_gt : Transitive gt
  := fun x y z p q => transitive_lt _ _ _ q p.
Global Instance ishprop_gt n m : IsHProp (gt n m) := _.
Global Instance decidable_gt n m : Decidable (gt n m) := _.

(** ** Properties of Subtraction *)

(** Subtracting a number from [0] is [0]. *)
Definition nat_sub_zero_l@{} n : 0 - n = 0 := idpath.

(** Subtracting [0] from a number is the number itself. *)
Definition nat_sub_zero_r@{} (n : nat) : n - 0 = n.
Proof.
  destruct n; reflexivity.
Defined.

(** Subtracting a number from itself is [0]. *)
Definition nat_sub_cancel@{} (n : nat) : n - n = 0.
Proof.
  simple_induction n n IHn.
  - reflexivity.
  - exact IHn.
Defined.

(** Subtracting an addition is the same as subtracting the two numbers separately. *)
Definition nat_sub_add@{} n m k : n - (m + k) = n - m - k.
Proof.
  induction n as [|n IHn] in m, k |- *.
  - reflexivity.
  - destruct m.
    + reflexivity.
    + nrapply IHn.
Defined. 

(** The order in which two numbers are subtracted does not matter. *)
Definition nat_sub_comm_r@{} n m k : n - m - k = n - k - m.
Proof.
  lhs_V nrapply nat_sub_add.
  rewrite nat_add_comm.
  nrapply nat_sub_add.
Defined.

(** Subtracting a larger number from a smaller number is [0]. *)
Definition equiv_nat_sub_leq {n m} : n <= m <~> n - m = 0.
Proof.
  srapply equiv_iff_hprop.
  - intro l; induction l.
    + exact (nat_sub_cancel n).
    + change (m.+1) with (1 + m). 
      lhs nrapply nat_sub_add.
      lhs nrapply nat_sub_comm_r.
      by destruct IHl^.
  - induction n as [|n IHn] in m |- *.
    1: intro; exact _.
    destruct m.
    + intros p; by destruct p.
    + intros p.
      apply leq_succ, IHn.
      exact p.
Defined.

(** We can cancel a left summand when subtracting it from a sum. *)
Definition nat_add_sub_cancel_l m n : n + m - n = m.
Proof. 
  induction n as [|n IHn].
  - nrapply nat_sub_zero_r.
  - exact IHn.
Defined.

(** We can cancel a right summand when subtracting it from a sum. *)
Definition nat_add_sub_cancel_r m n : m + n - n = m.
Proof.
  rhs_V nrapply (nat_add_sub_cancel_l m n).
  nrapply (ap (fun x => x - n)).
  nrapply nat_add_comm.
Defined.

(** We can move a subtracted number to the left-hand side of an equation. *)
Definition nat_moveL_nV {k m} n : k + n = m -> k = m - n.
Proof.
  intros p.
  destruct p.
  symmetry.
  apply nat_add_sub_cancel_r.
Defined.

(** We can move a subtracted number to the right-hand side of an equation. *)
Definition nat_moveR_nV {k m} n : k = n + m -> k - m = n
  := fun p => (nat_moveL_nV _ p^)^.

(** ** Properties of Maximum and Minimum *) 

(** *** Properties of Maxima *)

(** [nat_max] is idempotent. *)
Definition nat_max_idem@{} n : nat_max n n = n.
Proof.
  simple_induction' n; cbn.
  1: reflexivity.
  exact (ap S IH).
Defined.

(** [nat_max] is commutative. *)
Definition nat_max_comm@{} n m : nat_max n m = nat_max m n.
Proof.
  induction n as [|n IHn] in m |- *; destruct m; cbn.
  1-3: reflexivity.
  exact (ap S (IHn _)).
Defined.

(** The maximum of [n.+1] and [n] is [n.+1]. *)
Definition nat_max_succ_l@{} n : nat_max n.+1 n = n.+1.
Proof.
  simple_induction' n; cbn.
  1: reflexivity.
  exact (ap S IH).
Defined.

(** The maximum of [n] and [n.+1] is [n.+1]. *)
Definition nat_max_succ_r@{} n : nat_max n n.+1 = n.+1
  := nat_max_comm _ _ @ nat_max_succ_l _.

(** [0] is the left identity of [nat_max]. *)
Definition nat_max_zero_l@{} n : nat_max 0 n = n := idpath.

(** [0] is the right identity of [nat_max]. *)
Definition nat_max_zero_r@{} n : nat_max n 0 = n
  := nat_max_comm _ _ @ nat_max_zero_l _.

(** [nat_max n m] is [n] if [m <= n]. *) 
Definition nat_max_l@{} {n m} : m <= n -> nat_max n m = n.
Proof.
  intros H.
  induction m as [|m IHm] in n, H |- *.
  1: nrapply nat_max_zero_r.
  destruct n.
  1: inversion H.
  cbn; by apply (ap S), IHm, leq_succ'.
Defined.

(** [nat_max n m] is [m] if [n <= m]. *)
Definition nat_max_r {n m} : n <= m -> nat_max n m = m
  := fun _ => nat_max_comm _ _ @ nat_max_l _.

(** [nat_max n m] is associative. *)
Definition nat_max_assoc@{} n m k
  : nat_max n (nat_max m k) = nat_max (nat_max n m) k.
Proof.
  induction n as [|n IHn] in m, k |- *.
  1: reflexivity.
  destruct m, k.
  1-3: reflexivity.
  by apply (ap S), IHn.
Defined.

(** Properties of Minima *)

(** [nat_min] is idempotent. *)
Definition nat_min_idem n : nat_min n n = n.
Proof.
  simple_induction' n; cbn.
  1: reflexivity.
  exact (ap S IH).
Defined.

(** [nat_min] is commutative. *)
Definition nat_min_comm n m : nat_min n m = nat_min m n.
Proof.
  induction n as [|n IHn] in m |- *; destruct m; cbn.
  1-3: reflexivity.
  exact (ap S (IHn _)).
Defined.

(** [nat_min] of [0] and [n] is [0]. *)
Definition nat_min_zero_l n : nat_min 0 n = 0 := idpath.

(** [nat_min] of [n] and [0] is [0]. *)
Definition nat_min_zero_r n : nat_min n 0 = 0:= 
  nat_min_comm _ _ @ nat_min_zero_l _.

(** [nat_min n m] is [n] if [n <= m]. *)
Definition nat_min_l {n m} : n <= m -> nat_min n m = n.
Proof.
  revert n m.
  simple_induction n n IHn; auto.
  intros [] p.
  1: inversion p.
  cbn; by apply (ap S), IHn, leq_succ'.
Defined.

(** [nat_min n m] is [m] if [m <= n]. *)
Definition nat_min_r {n m} : m <= n -> nat_min n m = m
  := fun _ => nat_min_comm _ _ @ nat_min_l _.

(** [nat_min n m] is associative. *)
Definition nat_min_assoc n m k
  : nat_min n (nat_min m k) = nat_min (nat_min n m) k.
Proof.
  induction n as [|n IHn] in m, k |- *.
  1: reflexivity.
  destruct m, k.
  1-3: reflexivity.
  by apply (ap S), IHn.
Defined.

(** ** More Theory of Comparison Predicates *)

(** The first summand is less than or equal to the sum. *)
Definition leq_add_l n m : n <= n + m.
Proof.
  simple_induction n n IHn.
  - exact (leq_zero m).
  - exact (leq_succ IHn).
Defined.

(** The second summand is less than or equal to the sum. *)
Definition leq_add_r n m : n <= m + n.
Proof.
  simple_induction m m IH.
  - exact (leq_refl n).
  - exact (leq_succ_r IH).
Defined.

(** [<=] is an antisymmetric relation. *)
Definition leq_antisym {x y} : x <= y -> y <= x -> x = y.
Proof.
  intros p q.
  destruct p.
  1: reflexivity.
  destruct x; [inversion q|].
  apply leq_succ' in q.
  contradiction (not_leq_Sn_n _ (leq_trans p q)).
Defined.

Global Instance antisymmetric_leq : AntiSymmetric leq := @leq_antisym.

(** TODO: rename to [lt_irrefl] *)
(** [<] is an irreflexive relation. *)
Definition not_lt_n_n n : ~ (n < n) := not_leq_Sn_n n.
Global Instance irreflexive_lt : Irreflexive lt := not_lt_n_n.

(** TODO: rename *)
(** [1] is less than or equal to the successor of any number. *)
Definition leq_1_Sn {n} : 1 <= n.+1 := leq_succ (leq_zero _).

(** TODO: rename *)
Fixpoint leq_dichot {m} {n} : (m <= n) + (m > n).
Proof.
  simple_induction' m; simple_induction' n.
  - left; reflexivity.
  - left; apply leq_zero.
  - right; unfold lt; apply leq_1_Sn.
  - assert ((m <= n) + (n < m)) as X by apply leq_dichot.
    destruct X as [leqmn|ltnm].
    + left; apply leq_succ; assumption.
    + right; apply leq_succ; assumption.
Defined.

(** TODO: rename *)
Lemma not_lt_n_0 n : ~ (n < 0).
Proof.
  apply not_leq_Sn_0.
Defined.

(** TODO: rename *)
Definition not_lt_implies_geq {n m : nat} : ~(n < m) -> m <= n.
Proof.
  intros not_lt.
  destruct (@leq_dichot m n); [ assumption | contradiction].
Defined.

(** TODO: rename *)
Definition not_leq_implies_gt {n m : nat} : ~(n <= m) -> m < n.
Proof.
  intros not_leq. 
  destruct (@leq_dichot n m); [ contradiction | assumption].
Defined.

(** TODO: rename *)
Definition lt_implies_not_geq {n m : nat} : (n < m) -> ~(m <= n).
Proof.
  intros ineq1 ineq2.
  contradiction (not_lt_n_n n). by apply (leq_trans ineq1).
Defined.

(** TODO: rename *)
Definition leq_implies_not_gt {n m : nat} : (n <= m) -> ~(m < n).
Proof.
  intros ineq1 ineq2.
  contradiction (not_lt_n_n n); by refine (leq_trans _ ineq2).
Defined.

(** [n <= m] is equivalent to [(n < m) + (n = m)]. Note that it is not immediately obvious that the latter type is a hprop, hence we have to explicitly show the back and forth maps are inverses of eachother. This is possible and justifies the name "less than or equal to". *)
Definition equiv_leq_lt_or_eq {n m : nat} : (n <= m) <~> (n < m) + (n = m).
Proof.
  snrapply equiv_adjointify.
  - intro l; induction l.
    + now right.
    + left; exact (leq_succ l).
  - intros [l|p].
    + exact (leq_succ_l l).
    + destruct p.
      exact (leq_refl _).
  - intros [l|p].
    + induction l.
      1: reflexivity.
      snrapply (ap (inl)).
      rapply path_ishprop.
    + by destruct p.
  - intro; rapply path_ishprop.
Defined.

(** The inequality of natural numbers is equivalent to [n < m] or [n > m]. This could be an equivalence however one of the sections requires funext since we are comparing two inequality proofs. It is therefore more useful to keep it as a biimplication. *)
Definition neq_iff_lt_or_gt {n m} : n <> m <-> (n < m) + (n > m).
Proof.
  split.
  - intros diseq.
    destruct (dec (n < m)) as [| a]; [ now left |].
    apply not_lt_implies_geq in a.
    apply equiv_leq_lt_or_eq in a.
    destruct a as [lt | eq].
    1: by right.
    symmetry in eq.
    contradiction.
  - intros [H' | H'] nq; destruct nq; exact (not_lt_n_n _ H').
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

(** ** Properties of Powers *)

(** [0] to any power is [0] unless that power is [0] in which case it is [1]. *)
Definition nat_pow_zero_l@{} n : nat_pow 0 n = if dec (n = 0) then 1 else 0.
Proof.
  destruct n; reflexivity.
Defined.

(** Any number to the power of [0] is [1]. *)
Definition nat_pow_zero_r@{} n : nat_pow n 0 = 1
  := idpath.

(** [1] to any power is [1]. *)
Definition nat_pow_one_l@{} n : nat_pow 1 n = 1.
Proof.
  induction n as [|n IHn]; simpl.
  1: reflexivity.
  lhs nrapply nat_add_zero_r.
  exact IHn.
Defined.

(** Any number to the power of [1] is itself. *)
Definition nat_pow_one_r@{} n : nat_pow n 1 = n
  := nat_mul_one_r _.

(** Exponentiation of natural numbers is distributive over addition on the left. *)
Definition nat_pow_add_r@{} n m k
  : nat_pow n (m + k) = nat_pow n m * nat_pow n k.
Proof.
  induction m as [|m IHm]; simpl.
  - symmetry.
    apply nat_add_zero_r.
  - rhs_V nrapply nat_mul_assoc. 
    exact (ap _ IHm).
Defined.

(** Exponentiation of natural numbers is distributive over multiplication on the right. *)
Definition nat_pow_mul_l@{} n m k
  : nat_pow (n * m) k = nat_pow n k * nat_pow m k.
Proof.
  induction k as [|k IHk]; simpl.
  1: reflexivity.
  lhs_V nrapply nat_mul_assoc.
  rhs_V nrapply nat_mul_assoc.
  nrapply ap.
  rhs nrapply nat_mul_comm.
  rhs_V nrapply nat_mul_assoc.
  nrapply ap.
  rhs nrapply nat_mul_comm.
  exact IHk.
Defined.

(** Exponentiation of natural numbers is distributive over multiplication on the left. *)
Definition nat_pow_mul_r@{} n m k
  : nat_pow n (m * k) = nat_pow (nat_pow n m) k.
Proof.
  induction m as [|m IHm]; simpl.
  - exact (nat_pow_one_l _)^.
  - lhs nrapply nat_pow_add_r.
    rhs nrapply nat_pow_mul_l.
    nrapply ap.
    exact IHm.
Defined.
