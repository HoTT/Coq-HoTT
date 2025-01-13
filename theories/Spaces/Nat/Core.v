Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids
  Basics.Decidable Basics.Trunc Basics.Equivalences Basics.Nat
  Basics.Classes Basics.Iff Types.Prod Types.Sum Types.Sigma.
Export Basics.Nat.

Local Set Universe Minimization ToSet.
Local Unset Elimination Schemes.

(** * Natural numbers *)

(** We want to close the trunc_scope so that notations from there don't conflict here. *)
Local Close Scope trunc_scope.
Local Open Scope nat_scope.

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

(** This division takes time linear in `x` and is tail-recursive. In [nat_div_mod x y q u], [x + y.+1 * q + (y - u)] is the quantity being divided and [y] is the predecessor of the divisor.  It will be called with [q] zero and [u] equal to [y], so that [x] is the quantity being divided.  The return value is a pair [(q', u')] with [x + y.+1 * q + (y - u) = y.+1 * q' + (y - u')], at least when [u <= y], as shown in [nat_div_mod_spec_helper] in Nat/Divison.v. *)

Fixpoint nat_div_mod x y q u : nat * nat :=
  match x with
  | 0 => (q , u)
  | S x' =>
    match u with
    | 0 => nat_div_mod x' y (S q) y
    | S u' => nat_div_mod x' y q u'
    end
  end.

Definition nat_div x y : nat :=
  match y with
  | 0 => y
  | S y' => fst (nat_div_mod x y' 0 y')
  end.
Infix "/" := nat_div : nat_scope.

(** [nat_mod x y] is the remainder when [x] is divided by [y].  When [y] is zero, it is defined to be [x]. See [nat_div_mod_spec] and related results below. *)
Definition nat_mod x y : nat :=
  match y with
  | 0 => x
  | S y' => y' - snd (nat_div_mod x y' 0 y')
  end.
Infix "mod" := nat_mod : nat_scope.

(** For results about division and modulo, see Nat/Division.v. *)

(** *** Greatest common divisor *)

(** We use Euclid algorithm, which is normally not structural, but Coq is now clever enough to accept this (behind modulo there is a subtraction, which now preserves being a subterm) *)

Fixpoint nat_gcd a b :=
  match a with
  | O => b
  | S a' => nat_gcd (b mod a'.+1) a'.+1
  end.

(** ** Comparison predicates *)

(** *** Less than or equal To [<=] *)

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

(** *** Less than [<] *)

(** We define the less-than relation [lt] in terms of [leq] *)
Definition lt n m : Type0 := leq (S n) m.

(** We declare it as an existing class so typeclass search is performed on its goals. *)
Existing Class lt.
#[export] Hint Unfold lt : typeclass_instances.
Infix "<" := lt : nat_scope.
Global Instance lt_is_leq n m : leq n.+1 m -> lt n m | 100 := idmap.

(** *** Greater than or equal To [>=] *)

Definition geq n m := leq m n.
Existing Class geq.
#[export] Hint Unfold geq : typeclass_instances.
Infix ">=" := geq : nat_scope.
Global Instance geq_is_leq n m : leq m n -> geq n m | 100 := idmap.

(*** Greater Than [>] *)

Definition gt n m := lt m n.
Existing Class gt.
#[export] Hint Unfold gt : typeclass_instances.
Infix ">" := gt : nat_scope.
Global Instance gt_is_leq n m : leq m.+1 n -> gt n m | 100 := idmap.

(** *** Combined comparison predicates *)

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : nat_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : nat_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : nat_scope.

(** ** Properties of [nat_iter]. *)

Definition nat_iter_succ_r n {A} (f : A -> A) (x : A)
  : nat_iter (S n) f x = nat_iter n f (f x).
Proof.
  simple_induction n n IHn; simpl; trivial.
  exact (ap f IHn).
Defined.

Definition nat_iter_add (n m : nat) {A} (f : A -> A) (x : A)
  : nat_iter (n + m) f x = nat_iter n f (nat_iter m f x).
Proof.
  simple_induction n n IHn; simpl; trivial.
  exact (ap f IHn).
Defined.

(** Preservation of invariants : if [f : A -> A] preserves the invariant [P], then the iterates of [f] also preserve it. *)
Definition nat_iter_invariant (n : nat) {A} (f : A -> A) (P : A -> Type)
  : (forall x, P x -> P (f x)) -> forall x, P x -> P (nat_iter n f x).
Proof.
  simple_induction n n IHn; simpl; trivial.
  intros Hf x Hx.
  apply Hf, IHn; trivial.
Defined.

(** ** Properties of successors *)

(** The predecessor of a successor is the original number. *)
Definition nat_pred_succ@{} n : nat_pred (nat_succ n) = n
  := idpath.

(** The successor of a predecessor is the original as long as there is a strict lower bound. *)
Definition nat_succ_pred'@{} n i : i < n -> nat_succ (nat_pred n) = n.
Proof.
  by intros [].
Defined.

(** The most common lower bound is to take [0]. *)
Definition nat_succ_pred@{} n : 0 < n -> nat_succ (nat_pred n) = n
  := nat_succ_pred' n 0.

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
Definition neq_nat_succ'@{} n : n <> S n.
Proof.
  simple_induction' n.
  - apply neq_nat_zero_succ.
  - by apply neq_nat_succ.
Defined.

(** ** Truncatedness of natural numbers *)

(** [nat] has decidable paths. *)
Global Instance decidable_paths_nat@{} : DecidablePaths nat.
Proof.
  intros n m.
  induction n as [|n IHn] in m |- *; destruct m.
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

(** A sum being zero is equivalent to both summands being zero. *)
Definition equiv_nat_add_zero n m : n = 0 /\ m = 0 <~> n + m = 0.
Proof.
  srapply equiv_iff_hprop.
  - intros [-> ->]; reflexivity.
  - destruct n.
    + by split.
    + intros H; symmetry in H.
      by apply neq_nat_zero_succ in H.
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

(** ** Basic properties of comparison predicates *)

(** *** Basic properties of [<=] *)

(** [<=] is reflexive by definition. *)
Global Instance reflexive_leq : Reflexive leq := leq_refl.

(** Being less than or equal to is a transitive relation. *)
Definition leq_trans {x y z} : x <= y -> y <= z -> x <= z.
Proof.
  intros H1 H2; induction H2; exact _.
Defined.
Hint Immediate leq_trans : typeclass_instances.

(** [<=] is transtiive. *)
Global Instance transitive_leq : Transitive leq := @leq_trans.

(** [0] is less than or equal to any natural number. *)
Definition leq_zero_l n : 0 <= n.
Proof.
  simple_induction' n; exact _.
Defined.
Global Existing Instance leq_zero_l | 10.

(** A predecessor is less than or equal to a predecessor if the original number is less than or equal. *)
Global Instance leq_pred {n m} : n <= m -> nat_pred n <= nat_pred m.
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
Definition leq_pred' {n m} : n.+1 <= m.+1 -> n <= m := leq_pred.
Hint Immediate leq_pred' : typeclass_instances.

(** [<] is an irreflexive relation. *)
Definition lt_irrefl n : ~ (n < n).
Proof.
  induction n as [|n IHn].
  1: intro p; inversion p.
  intros p; by apply IHn, leq_pred'.
Defined.

Global Instance irreflexive_lt : Irreflexive lt := lt_irrefl.
Global Instance irreflexive_gt : Irreflexive gt := lt_irrefl.

(** [<=] is an antisymmetric relation. *)
Definition leq_antisym {x y} : x <= y -> y <= x -> x = y.
Proof.
  intros p q.
  destruct p.
  1: reflexivity.
  destruct x; [inversion q|].
  apply leq_pred' in q.
  contradiction (lt_irrefl _ (leq_trans p q)).
Defined.

Global Instance antisymmetric_leq : AntiSymmetric leq := @leq_antisym.
Global Instance antisymemtric_geq : AntiSymmetric geq
  := fun _ _ p q => leq_antisym q p.

(** Every natural number is zero or greater than zero. *)
Definition nat_zero_or_gt_zero n : (0 = n) + (0 < n).
Proof.
  induction n as [|n IHn].
  1: left; reflexivity.
  right; exact _.
Defined.

(** Being less than or equal to [0] implies being [0]. *)
Definition path_zero_leq_zero_r n : n <= 0 -> n = 0.
Proof.
  intros H; rapply leq_antisym.
Defined.

(** Nothing can be less than [0]. *)
Definition not_lt_zero_r n : ~ (n < 0).
Proof.
  intros p.
  apply (lt_irrefl n), (leq_trans p).
  exact _.
Defined.

(** A general form for injectivity of this constructor *)
Definition leq_refl_inj_gen n k (p : n <= k) (r : n = k) : p = r # leq_refl n.
Proof.
  destruct p.
  + assert (c : idpath = r) by apply path_ishprop.
    destruct c.
    reflexivity.
  + destruct r^.
    contradiction (lt_irrefl _ p).
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
    contradiction (lt_irrefl _ p).
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
Defined.

Global Instance decidable_leq n m : Decidable (n <= m).
Proof.
  revert n.
  simple_induction' m; intros n.
  - destruct n.
    + left; exact _.
    + right; apply not_lt_zero_r.
  - destruct n.
    + left; exact _.
    + rapply decidable_equiv'.
      symmetry.
      apply equiv_leq_succ.
Defined.

(** [n.+1 <= m] implies [n <= m]. *)
Definition leq_succ_l {n m} : n.+1 <= m -> n <= m.
Proof.
  intro l; apply leq_pred'; exact _.
Defined.

(** *** Basic properties of [<] *)

(** [<=] and [<] imply [<] *)
Definition lt_leq_lt_trans {n m k} : n <= m -> m < k -> n < k
  := fun leq lt => leq_trans (leq_succ leq) lt.

(** [<=] and [<] imply [<] *)
Definition lt_lt_leq_trans {n m k} : n < m -> m <= k -> n < k
  := fun lt leq => leq_trans lt leq.

Definition leq_lt {n m} : n < m -> n <= m
  := leq_succ_l.
Hint Immediate leq_lt : typeclass_instances.

Definition lt_trans {n m k} : n < m -> m < k -> n < k
  := fun H1 H2 => leq_lt (lt_leq_lt_trans H1 H2).
Hint Immediate lt_trans : typeclass_instances.

Global Instance transitive_lt : Transitive lt := @lt_trans.
Global Instance ishprop_lt n m : IsHProp (n < m) := _.
Global Instance decidable_lt n m : Decidable (lt n m) := _.

(** *** Basic properties of [>=] *)

Global Instance reflexive_geq : Reflexive geq := leq_refl.
Global Instance transitive_geq : Transitive geq := fun x y z p q => leq_trans q p.
Global Instance ishprop_geq n m : IsHProp (geq n m) := _.
Global Instance decidable_geq n m : Decidable (geq n m) := _.

(** *** Basic properties of [>] *)

Global Instance transitive_gt : Transitive gt
  := fun x y z p q => transitive_lt _ _ _ q p.
Global Instance ishprop_gt n m : IsHProp (gt n m) := _.
Global Instance decidable_gt n m : Decidable (gt n m) := _.

(** ** Properties of subtraction *)

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
Definition nat_sub_r_add@{} n m k : n - (m + k) = n - m - k.
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
  lhs_V nrapply nat_sub_r_add.
  rewrite nat_add_comm.
  nrapply nat_sub_r_add.
Defined.

(** Subtracting a larger number from a smaller number is [0]. *)
Definition equiv_nat_sub_leq {n m} : n <= m <~> n - m = 0.
Proof.
  srapply equiv_iff_hprop.
  - intro l; induction l.
    + exact (nat_sub_cancel n).
    + change (m.+1) with (1 + m).
      lhs nrapply nat_sub_r_add.
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

(** We can cancel a right subtrahend when adding it on the right to a subtraction if the subtrahend is less than the number being subtracted from. *)
Definition nat_add_sub_l_cancel {n m} : n <= m -> (m - n) + n = m.
Proof.
  intros H.
  induction n as [|n IHn] in m, H |- *.
  - lhs nrapply nat_add_zero_r.
    nrapply nat_sub_zero_r.
  - destruct m.
    1: contradiction (not_lt_zero_r n).
    lhs nrapply nat_add_succ_r.
    nrapply (ap nat_succ).
    nrapply IHn.
    exact (leq_pred' H).
Defined.

(** We can cancel a right subtrahend when adding it on the left to a subtraction if the subtrahend is less than the nubmer being subtracted from. *)
Definition nat_add_sub_r_cancel {n m} : n <= m -> n + (m - n) = m.
Proof.
  intros H.
  rhs_V nrapply (nat_add_sub_l_cancel H).
  apply nat_add_comm.
Defined.

(** We can move a subtracted number to the left-hand side of an equation. *)
Definition nat_moveL_nV {n m} k : n + k = m -> n = m - k.
Proof.
  intros p.
  destruct p.
  symmetry.
  apply nat_add_sub_cancel_r.
Defined.

(** We can move a subtracted number to the right-hand side of an equation. *)
Definition nat_moveR_nV {n m} k : n = m + k -> n - k = m
  := fun p => (nat_moveL_nV _ p^)^.

(** Subtracting a successor is the predecessor of subtracting the original number. *)
Definition nat_sub_succ_r n m : n - m.+1 = nat_pred (n - m).
Proof.
  induction n as [|n IHn] in m |- *.
  1: reflexivity.
  destruct m.
  1: apply nat_sub_zero_r.
  apply IHn.
Defined.

(** ** Properties of maximum and minimum *)

(** *** Properties of maximum *)

(** [nat_max] is idempotent. *)
Definition nat_max_idem@{} n : nat_max n n = n.
Proof.
  simple_induction' n; cbn.
  1: reflexivity.
  exact (ap S IH).
Defined.

(** The defining properties of [nat_max]: [m] and [n] are less than or equal to [nat_max n m] and [nat_max n m] is less than or equal to any number greater than or equal to [m] and [n]. *)
Definition leq_nat_max_l@{} n m : n <= nat_max n m.
Proof.
  induction n as [|n IHn] in m |- *.
  1: exact (leq_zero_l _).
  destruct m; cbn.
  1: cbn; reflexivity.
  exact (leq_succ (IHn m)).
Defined.

Definition leq_nat_max_r@{} n m : m <= nat_max n m.
Proof.
  induction n as [|n IHn] in m |- *.
  1: cbn; reflexivity.
  destruct m; cbn.
  1: exact (leq_zero_l _).
  exact (leq_succ (IHn m)).
Defined.

Definition leq_nat_max@{} {n m k : nat} (Hn : n <= k) (Hm : m <= k)
  : nat_max n m <= k.
Proof.
  induction k in m, n, Hn, Hm |- *; destruct m, n; cbn.
  1-3, 5-7: exact _.
  - contradiction (not_lt_zero_r _ _).
  - exact (leq_succ (IHk n m _ _)).
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
  cbn; by apply (ap S), IHm, leq_pred'.
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

(** The defining properties of [nat_min]: [nat_min n m] is less than or equal to [m] and [n] and any number less than or equal to [m] and [n] is less than or equal to [nat_min n m]. *)
Definition leq_nat_min_l@{} n m : nat_min n m <= n.
Proof.
  induction n as [|n IHn] in m |- *.
  1: cbn; reflexivity.
  destruct m; cbn.
  1: exact (leq_zero_l _).
  exact (leq_succ (IHn m)).
Defined.

Definition leq_nat_min_r@{} n m : nat_min n m <= m.
Proof.
  induction n as [|n IHn] in m |- *.
  1: exact (leq_zero_l _).
  destruct m; cbn.
  1: cbn; reflexivity.
  exact (leq_succ (IHn m)).
Defined.

Definition leq_nat_min@{} {n m k : nat} (Hn : k <= n) (Hm : k <= m)
  : k <= nat_min n m.
Proof.
  induction k in m, n, Hn, Hm |- *; destruct m, n; cbn.
  1-7: exact _.
  exact (leq_succ (IHk n m _ _)).
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
  cbn; by apply (ap S), IHn, leq_pred'.
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

(** ** More theory of comparison predicates *)

(** *** Addition lemmas *)

(** The second summand is less than or equal to the sum. *)
Global Instance leq_add_l n m : n <= m + n.
Proof.
  simple_induction m m IH.
  - exact (leq_refl n).
  - exact (leq_succ_r IH).
Defined.

(** The first summand is less than or equal to the sum. *)
Global Instance leq_add_r n m : n <= n + m.
Proof.
  simple_induction n n IHn.
  - exact (leq_zero_l m).
  - exact (leq_succ IHn).
Defined.

(** *** Multiplication lemmas *)

(** The second multiplicand is less than or equal to the product. *)
Global Instance leq_mul_l n m l : l < m -> n <= m * n.
Proof.
  intros H; induction H; exact _.
Defined.

(** The first multiplicand is less than or equal to the product. *)
Global Instance leq_mul_r n m l : l < m -> n <= n * m.
Proof.
  rewrite nat_mul_comm; exact _.
Defined.

(** ** Eliminating positive assumptions *)

(** Sometimes we want to prove a predicate which assumes that [0 < x]. In that case, it suffices to prove it for [x.+1] instead. *)
Definition gt_zero_ind (P : nat -> Type)
  (H : forall x, P x.+1)
  : forall x (l : 0 < x), P x.
Proof.
  intros x l.
  destruct x.
  1: contradiction (lt_irrefl _ l).
  apply H.
Defined.

(** Alternative Characterizations of [<=] *)

(** [n <= m] is equivalent to [(n < m) + (n = m)]. This justifies the name "less than or equal to". Note that it is not immediately obvious that the latter type is a hprop. *)
Definition equiv_leq_lt_or_eq {n m} : (n <= m) <~> (n < m) + (n = m).
Proof.
  srapply equiv_iff_hprop.
  - nrapply ishprop_sum.
    1,2: exact _.
    intros H1 p; destruct p.
    contradiction (lt_irrefl _ _).
  - intro l; induction l.
    + by right.
    + left; exact (leq_succ l).
  - intros [l|p].
    + exact (leq_succ_l l).
    + destruct p.
      exact (leq_refl _).
Defined.

(** Here is an alternative characterization of [<=] in terms of an existence predicate and addition. *)
Definition equiv_leq_add n m : n <= m <~> exists k, k + n = m.
Proof.
  srapply equiv_iff_hprop.
  - apply hprop_allpath.
    intros [x p] [y q].
    pose (r := nat_moveL_nV _ p @ (nat_moveL_nV _ q)^).
    destruct r.
    apply ap.
    apply path_ishprop.
  - intros p.
    exists (m - n).
    apply nat_add_sub_l_cancel, p.
  - intros [k p].
    destruct p.
    apply leq_add_l.
Defined.

(** *** Dichotomy of [<=] *)

Definition leq_dichotomy m n : (m <= n) + (m > n).
Proof.
  induction m as [|m IHm] in n |- *.
  1: left; exact _.
  destruct n.
  1: right; exact _.
  destruct (IHm n).
  1: left; exact _.
  1: right; exact _.
Defined.

(** *** Trichotomy *)

(** Any two natural numbers are either equal, less than, or greater than each other. *)
Definition nat_trichotomy m n : (m < n) + (m = n) + (m > n).
Proof.
  generalize (leq_dichotomy m n).
  snrapply (functor_sum _ idmap).
  snrapply equiv_leq_lt_or_eq.
Defined.

(** *** Negation lemmas *)

(** There are various lemmas we can state about negating the comparison operators on [nat]. To aid readability, we opt to keep the order of the variables in each statement consistent. *)

Definition geq_iff_not_lt {n m} : ~(n < m) <-> n >= m.
Proof.
  split.
  - intro; by destruct (leq_dichotomy m n).
  - intros ? ?; contradiction (lt_irrefl n); exact _.
Defined.

Definition gt_iff_not_leq {n m} : ~(n <= m) <-> n > m.
Proof.
  split.
  - intro; by destruct (leq_dichotomy n m).
  - intros ? ?; contradiction (lt_irrefl m); exact _.
Defined.

Definition leq_iff_not_gt {n m} : ~(n > m) <-> n <= m
  := geq_iff_not_lt.

Definition lt_iff_not_geq {n m} : ~(n >= m) <-> n < m
  := gt_iff_not_leq.

(** *** Dichotomy of [<>] *)

(** The inequality of natural numbers is equivalent to [n < m] or [n > m]. This could be an equivalence however one of the sections requires funext since we are comparing two inequality proofs. It is therefore more useful to keep it as a biimplication. Note that this is a negated version of antisymmetry of [<=]. *)
Definition neq_iff_lt_or_gt {n m} : n <> m <-> (n < m) + (n > m).
Proof.
  split.
  - intros diseq.
    destruct (dec (n < m)) as [| a]; [ by left |].
    apply geq_iff_not_lt in a.
    apply equiv_leq_lt_or_eq in a.
    destruct a as [lt | eq].
    1: by right.
    symmetry in eq.
    contradiction.
  - intros [H' | H'] nq; destruct nq; exact (lt_irrefl _ H').
Defined.

(** ** Arithmetic relations between [trunc_index] and [nat]. *)

Definition trunc_index_add_nat_add {n : nat}: trunc_index_add n n = n.+1 + n.+1.
Proof.
  induction n as [|n IHn].
  1: reflexivity.
  lhs nrapply trunc_index_add_succ.
  rhs nrapply (ap nat_to_trunc_index).
  2: nrapply nat_add_succ_r.
  exact (ap (fun x => x.+2%trunc) IHn).
Defined.

(** *** Subtraction *)

Global Instance leq_sub_add_l n m : n <= n - m + m.
Proof.
  destruct (@leq_dichotomy m n) as [l | g].
  - by rewrite nat_add_sub_l_cancel.
  - apply leq_lt in g.
    by destruct (equiv_nat_sub_leq _)^.
Defined.

Global Instance leq_sub_add_r n m : n <= m + (n - m).
Proof.
  rewrite nat_add_comm; exact _.
Defined.

(** A number being less than another is equivalent to their difference being greater than zero. *)
Definition equiv_lt_lt_sub n m : m < n <~> 0 < n - m.
Proof.
  induction n as [|n IHn] in m |- *.
  1: srapply equiv_iff_hprop; intro; contradiction (not_lt_zero_r _ _).
  destruct m; only 1: reflexivity.
  nrefine (IHn m oE _).
  srapply equiv_iff_hprop.
Defined.

(** *** Monotonicity of addition *)

(** TODO: use OrderPreserving from canonical_names *)

(** Addition on the left is monotone. *)
Definition nat_add_l_monotone {n m} k
  : n <= m -> k + n <= k + m.
Proof.
  intros H; induction k; exact _.
Defined.
Hint Immediate nat_add_l_monotone : typeclass_instances.

(** Addition on the right is monotone. *)
Definition nat_add_r_monotone {n m} k
  : n <= m -> n + k <= m + k.
Proof.
  intros H; rewrite 2 (nat_add_comm _ k); exact _.
Defined.
Hint Immediate nat_add_r_monotone : typeclass_instances.

(** Addition is monotone in both arguments. (This makes [+] a bifunctor when treating [nat] as a category (as a preorder)). *)
Definition nat_add_monotone {n n' m m'}
  : n <= m -> n' <= m' -> n + n' <= m + m'.
Proof.
  intros H1 H2; induction H1; exact _.
Defined.
Hint Immediate nat_add_monotone : typeclass_instances.

(** *** Strict monotonicity of addition *)

(** [nat_succ] is strictly monotone. *)
Global Instance lt_succ {n m} : n < m -> n.+1 < m.+1 := _.

Global Instance lt_succ_r {n m} : n < m -> n < m.+1 := _.

(** Addition on the left is strictly monotone. *)
Definition nat_add_l_strictly_monotone {n m} k
  : n < m -> k + n < k + m.
Proof.
  intros H; induction k; exact _.
Defined.
Hint Immediate nat_add_l_strictly_monotone : typeclass_instances.

(** Addition on the right is strictly monotone. *)
Definition nat_add_r_strictly_monotone {n m} k
  : n < m -> n + k < m + k.
Proof.
  intros H; rewrite 2 (nat_add_comm _ k); exact _.
Defined.
Hint Immediate nat_add_r_strictly_monotone : typeclass_instances.

(** Addition is strictly monotone in both arguments. *)
Definition nat_add_strictly_monotone {n n' m m'}
  : n < m -> n' < m' -> n + n' < m + m'.
Proof.
  intros H1 H2; induction H1; exact _.
Defined.
Hint Immediate nat_add_strictly_monotone : typeclass_instances.

(** *** Monotonicity of multiplication *)

(** Multiplication on the left is monotone. *)
Definition nat_mul_l_monotone {n m} k
  : n <= m -> k * n <= k * m.
Proof.
  intros H; induction k; exact _.
Defined.
Hint Immediate nat_mul_l_monotone : typeclass_instances.

(** Multiplication on the right is monotone. *)
Definition nat_mul_r_monotone {n m} k
  : n <= m -> n * k <= m * k.
Proof.
  intros H; rewrite 2 (nat_mul_comm _ k); exact _.
Defined.
Hint Immediate nat_mul_r_monotone : typeclass_instances.

(** Multiplication is monotone in both arguments. *)
Definition nat_mul_monotone {n n' m m'}
  : n <= m -> n' <= m' -> n * n' <= m * m'.
Proof.
  intros H1 H2; induction H1; exact _.
Defined.
Hint Immediate nat_mul_monotone : typeclass_instances.

(** *** Strict monotonicity of multiplication *)

(** Multiplication on the left by a positive number is strictly monotone. *)
Definition nat_mul_l_strictly_monotone {n m l} k
  : l < k -> n < m -> k * n < k * m.
Proof.
  destruct k.
  1: intro; contradiction (not_lt_zero_r _ H).
  intros _ H; induction k as [|k IHk] in |- *; exact _.
Defined.
Hint Immediate nat_mul_l_strictly_monotone : typeclass_instances.

(** Multiplication on the right by a positive number is strictly monotone. *)
Definition nat_mul_r_strictly_monotone {n m l} k
  : l < k -> n < m -> n * k < m * k.
Proof.
  intros ? H; rewrite 2 (nat_mul_comm _ k); exact _.
Defined.
Hint Immediate nat_mul_r_strictly_monotone : typeclass_instances.

(** Multiplication is strictly monotone in both arguments. *)
Definition nat_mul_strictly_monotone {n n' m m'}
  : n < m -> n' < m' -> n * n' < m * m'.
Proof.
  intros H1 H2.
  nrapply (lt_leq_lt_trans (m:=n * m')).
  1: rapply nat_mul_l_monotone.
  rapply nat_mul_r_strictly_monotone.
Defined.
Hint Immediate nat_mul_strictly_monotone : typeclass_instances.

(** *** Order-reflection *)

(** Addition on the left is order-reflecting. *)
Definition leq_reflects_add_l {n m} k : k + n <= k + m -> n <= m.
Proof.
  intros H; induction k; exact _.
Defined.

(** Addition on the right is order-reflecting. *)
Definition leq_reflects_add_r {n m} k : n + k <= m + k -> n <= m.
Proof.
  rewrite 2 (nat_add_comm _ k); nrapply leq_reflects_add_l.
Defined.

(** Addition on the left is strictly order-reflecting. *)
Definition lt_reflects_add_l {n m} k : k + n < k + m -> n < m.
Proof.
  intros H; induction k; exact _.
Defined.

(** Addition on the right is strictly order-reflecting. *)
Definition lt_reflects_add_r {n m} k : n + k < m + k -> n < m.
Proof.
  rewrite 2 (nat_add_comm _ k); nrapply lt_reflects_add_l.
Defined.

(** ** Further properties of subtraction *)

Global Instance leq_sub_l n m : n - m <= n.
Proof.
  apply equiv_nat_sub_leq.
  rewrite nat_sub_comm_r.
  rewrite nat_sub_cancel.
  apply nat_sub_zero_l.
Defined.

(** Subtracting from a successor is the successor of subtracting from the original number, as long as the amount being subtracted is less than or equal to the original number. *)
Definition nat_sub_succ_l n m : m <= n -> n.+1 - m = (n - m).+1.
Proof.
  intros H.
  induction m as [|m IHm] in n, H |- *.
  - by rewrite 2 nat_sub_zero_r.
  - simpl.
    rewrite nat_sub_succ_r.
    symmetry.
    apply nat_succ_pred.
    by apply equiv_lt_lt_sub.
Defined.

(** Under certain conditions, subtracting a predecessor is the successor of the subtraction. *)
Definition nat_sub_pred_r n m : 0 < m -> m < n -> n - nat_pred m = (n - m).+1.
Proof.
  revert m; snrapply gt_zero_ind.
  intros m H1.
  rewrite nat_sub_succ_r.
  rewrite nat_succ_pred.
  1: reflexivity.
  apply equiv_lt_lt_sub.
  exact (lt_trans _ H1).
Defined.

(** Subtracting from a sum is the sum of subtracting from the second summand. *)
Definition nat_sub_l_add_r m n k
  : k <= m -> (n + m) - k = n + (m - k).
Proof.
  intros H; induction n as [|n IHn] in |- *.
  - reflexivity.
  - change (?n.+1 + ?m) with (n + m).+1.
    lhs nrapply nat_sub_succ_l.
    2: exact (ap nat_succ IHn).
    exact _.
Defined.

(** Subtracting from a sum is the sum of subtracting from the first summand. *)
Definition nat_sub_l_add_l n m k
  : k <= n -> (n + m) - k = (n - k) + m.
Proof.
  intro l.
  rewrite nat_add_comm.
  lhs rapply nat_sub_l_add_r.
  apply nat_add_comm.
Defined.

(** Subtracting a subtraction is the subtrahend. *)
Definition nat_sub_sub_cancel_r {n m} : n <= m -> m - (m - n) = n.
Proof.
  intros H; induction H.
  - by rewrite nat_sub_cancel, nat_sub_zero_r.
  - rewrite (nat_sub_succ_l m n); only 2: exact _.
    exact IHleq.
Defined.

(** Multiplication on the left distributes over subtraction. *)
Definition nat_dist_sub_l n m k
  : n * (m - k) = n * m - n * k.
Proof.
  induction n as [|n IHn] in m, k |- *.
  1: reflexivity.
  destruct (leq_dichotomy k m) as [l|r].
  - simpl; rewrite IHn, <- nat_sub_l_add_r, <- nat_sub_l_add_l,
      nat_sub_r_add; trivial; exact _.
  - apply leq_lt in r.
    apply equiv_nat_sub_leq in r.
    rewrite r.
    rewrite nat_mul_zero_r.
    symmetry.
    apply equiv_nat_sub_leq.
    apply nat_mul_l_monotone.
    by apply equiv_nat_sub_leq.
Defined.

(** Multiplication on the right distributes over subtraction. *)
Definition nat_dist_sub_r n m k
  : (n - m) * k = n * k - m * k.
Proof.
  rewrite 3 (nat_mul_comm _ k).
  apply nat_dist_sub_l.
Defined.

(** *** Monotonicity of subtraction *)

(** Subtraction is monotone in the left argument. *)
Definition nat_sub_monotone_l {n m} k : n <= m -> n - k <= m - k.
Proof.
  intros H.
  destruct (leq_dichotomy k n) as [l|r].
  - apply (leq_reflects_add_l k).
    rewrite 2 nat_add_sub_r_cancel.
    + exact H.
    + rapply leq_trans.
    + exact l.
  - apply leq_succ_l in r.
    apply equiv_nat_sub_leq in r.
    destruct r^.
    exact _.
Defined.
Hint Immediate nat_sub_monotone_l : typeclass_instances.

(** Subtraction is contravariantly monotone in the right argument. *)
Definition nat_sub_monotone_r {n m} k : n <= m -> k - m <= k - n.
Proof.
  intros H.
  induction k.
  - by rewrite nat_sub_zero_l.
  - destruct (leq_dichotomy m k) as [l|r].
    + rewrite 2 nat_sub_succ_l; exact _.
    + apply equiv_nat_sub_leq in r.
      destruct r^.
      exact _.
Defined.
Hint Immediate nat_sub_monotone_r : typeclass_instances.

(** *** Order-reflection lemmas *)

(** Subtraction reflects [<=] in the left argument. *)
Definition leq_reflects_sub_l {n m} k : k <= m -> n - k <= m - k -> n <= m.
Proof.
  intros ineq1 ineq2.
  apply (nat_add_r_monotone k) in ineq2.
  apply (@leq_trans _ (n - k + k) _ (leq_sub_add_l _ _)).
  apply (@leq_trans _ (m - k + k) _ _).
  by rewrite nat_add_sub_l_cancel.
Defined.

(** Subtraction reflects [<=] in the right argument contravariantly. *)
Definition leq_reflects_sub_r {n m} k
  : m <= k -> n <= k -> k - n <= k - m -> m <= n.
Proof.
  intros H1 H2 H3.
  apply (nat_sub_monotone_r k) in H3.
  rewrite 2 nat_sub_sub_cancel_r in H3; exact _.
Defined.

(** *** Movement lemmas *)

(** Given an inequality [n < m] we can move around a summand or subtrahend [k] from either side. *)

Definition leq_moveL_Mn {n m} k : n - k <= m -> n <= k + m.
Proof.
  intros H.
  rewrite nat_add_comm.
  apply (nat_add_r_monotone k) in H.
  rapply leq_trans.
Defined.

Definition leq_moveL_nM {n m} k : n - k <= m -> n <= m + k.
Proof.
  rewrite nat_add_comm.
  apply leq_moveL_Mn.
Defined.

Definition leq_moveR_Mn {n m} k : k <= m -> n <= m - k -> k + n <= m.
Proof.
  intros H1 H2.
  rapply (leq_reflects_sub_l k).
  by rewrite nat_add_sub_cancel_l.
Defined.

Definition leq_moveR_nM {n m} k : k <= m -> n <= m - k -> n + k <= m.
Proof.
  rewrite nat_add_comm.
  apply leq_moveR_Mn.
Defined.

Definition leq_moveL_nV {n m} k : n + k <= m -> n <= m - k.
Proof.
  intros H.
  apply (leq_reflects_add_r k).
  rapply leq_trans.
Defined.

Definition leq_moveR_nV {n m} k : n <= m + k -> n - k <= m.
Proof.
  intros H.
  apply (nat_sub_monotone_l k) in H.
  by rewrite nat_add_sub_cancel_r in H.
Defined.

Definition lt_moveL_Mn {n m} k : n - k < m -> n < k + m.
Proof.
  intros H.
  apply (nat_add_l_strictly_monotone k) in H.
  rapply lt_leq_lt_trans.
Defined.

Definition lt_moveL_nM {n m} k : n - k < m -> n < m + k.
Proof.
  rewrite nat_add_comm.
  apply lt_moveL_Mn.
Defined.

Definition lt_moveR_Mn {n m} k : k < m -> n < m - k -> k + n < m.
Proof.
  intros H1 H2.
  rewrite nat_add_comm.
  rapply (leq_moveR_nM (n:=n.+1) k).
Defined.

Definition lt_moveR_nM {n m} k : k < m -> n < m - k -> n + k < m.
Proof.
  rewrite nat_add_comm.
  apply lt_moveR_Mn.
Defined.

Definition lt_moveL_nV {n m} k : n + k < m -> n < m - k.
Proof.
  intros H.
  rapply leq_moveL_nV.
Defined.

Definition lt_moveR_nV {n m} k : k <= n -> n < k + m -> n - k < m.
Proof.
  intros H1 H2; unfold lt.
  rewrite <- nat_sub_succ_l; only 2: exact _.
  rewrite <- (nat_add_sub_cancel_l m k).
  by apply nat_sub_monotone_l.
Defined.

(** ** Properties of powers *)

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

(** *** Monotonicity of powers *)

Definition nat_pow_l_monotone {n m} k
  : n <= m -> nat_pow k.+1 n <= nat_pow k.+1 m.
Proof.
  intros H; induction H; exact _.
Defined.

Definition nat_pow_r_monotone {n m} k
  : n <= m -> nat_pow n k <= nat_pow m k.
Proof.
  intros H; induction k; exact _.
Defined.

(** ** Strong induction *)

(** Sometimes using [nat_ind] is not sufficient to prove a statement as it may be difficult to prove [P n -> P n.+1]. We can strengthen the induction hypothesis by assuming that [P m] holds for all [m] less than [n]. This is known as strong induction. *)
Definition nat_ind_strong@{u} (P : nat -> Type@{u})
  (IH_strong : forall n, (forall m, m < n -> P m) -> P n)
  : forall n, P n.
Proof.
  intros n.
  apply IH_strong.
  simple_induction n n IHn; intros m H.
  1: contradiction (not_lt_zero_r m).
  apply leq_pred' in H.
  apply equiv_leq_lt_or_eq in H.
  destruct H as [H|p].
  - by apply IHn.
  - destruct p.
    by apply IH_strong.
Defined.

(** ** An induction principle for two variables with a constraint. *)
Definition nat_double_ind_leq@{u} (P : nat -> nat -> Type@{u})
  (Hn0 : forall n, P n 0)
  (Hnn : forall n, P n n)
  (IH : forall n m, m < n -> (forall m', m' <= n -> P n m') -> P n.+1 m.+1)
  : forall n m, m <= n -> P n m.
Proof.
  intro n; simple_induction n n IHn; intros m H.
  - destruct (path_zero_leq_zero_r m H)^; clear H.
    apply Hn0.
  - destruct m.
    + apply Hn0.
    + apply equiv_leq_lt_or_eq in H.
      destruct H as [H | []].
      2: apply Hnn.
      rapply IH.
      rapply IHn.
Defined.
