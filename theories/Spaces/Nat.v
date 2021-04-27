(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Export Basics.Nat.
Require Import HoTT.TruncType.
Require Export HoTT.DProp.

Local Unset Elimination Schemes.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rect := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.

(** * Theorems about the natural numbers *)

(** Many of these definitions and proofs have been ported from the coq stdlib. *)

(** We want to close the trunc_scope so that notations from there don't conflict here. *)
Local Close Scope trunc_scope.
Local Open Scope nat_scope.

(** ** Basic operations on naturals *)

(** It is common to call [S] [succ] so we add it as a parsing only notation. *)
Notation succ := S (only parsing).

(** The predecessor of a natural number. *)
Definition pred n : nat :=
  match n with
  | 0 => n
  | S n' => n'
  end.

(** Addition of natural numbers *)
Fixpoint add n m : nat :=
  match n with
  | 0 => m
  | S n' => S (add n' m)
  end.

Notation "n + m" := (add n m) : nat_scope.

Definition double n : nat := n + n.

Fixpoint mul n m : nat :=
  match n with
  | 0 => 0
  | S n' => m + (mul n' m)
  end.

Notation "n * m" := (mul n m) : nat_scope.

(** Truncated subtraction: [n - m] is [0] if [n <= m] *)
Fixpoint sub n m : nat :=
  match n, m with
  | S n' , S m' => sub n' m'
  | _ , _ => n
  end.

Notation "n - m" := (sub n m) : nat_scope.

(** ** Minimum, maximum *)

Fixpoint max n m :=
  match n, m with
  | 0 , _ => m
  | S n' , 0 => n'.+1
  | S n' , S m' => (max n' m').+1
  end.

Fixpoint min n m :=
  match n, m with
  | 0 , _ => 0
  | S n' , 0 => 0
  | S n' , S m' => S (min n' m')
  end.

(** ** Power *)

Fixpoint pow n m :=
  match m with
  | 0 => 1
  | S m' => n * (pow n m')
  end.

(** ** Euclidean division *)

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

(** ** Greatest common divisor *)

(** We use Euclid algorithm, which is normally not structural, but Coq is now clever enough to accept this (behind modulo there is a subtraction, which now preserves being a subterm) *)

Fixpoint gcd a b :=
  match a with
  | O => b
  | S a' => gcd (b mod a'.+1) a'.+1
  end.

(** ** Square *)

Definition square n : nat := n * n.

(** ** Square root *)

(** The following square root function is linear (and tail-recursive).
  With Peano representation, we can't do better. For faster algorithm,
  see Psqrt/Zsqrt/Nsqrt...

  We search the square root of n = k + p^2 + (q - r)
  with q = 2p and 0<=r<=q. We start with p=q=r=0, hence
  looking for the square root of n = k. Then we progressively
  decrease k and r. When k = S k' and r=0, it means we can use (S p)
  as new sqrt candidate, since (S k')+p^2+2p = k'+(S p)^2.
  When k reaches 0, we have found the biggest p^2 square contained
  in n, hence the square root of n is p.
*)

Fixpoint sqrt_iter k p q r : nat :=
  match k with
  | O => p
  | S k' =>
    match r with
    | O => sqrt_iter k' p.+1 q.+2 q.+2
    | S r' => sqrt_iter k' p q r'
    end
  end.

Definition sqrt n : nat := sqrt_iter n 0 0 0.

(** ** Log2 *)

(** This base-2 logarithm is linear and tail-recursive.

  In [log2_iter], we maintain the logarithm [p] of the counter [q],
  while [r] is the distance between [q] and the next power of 2,
  more precisely [q + S r = 2^(S p)] and [r<2^p]. At each
  recursive call, [q] goes up while [r] goes down. When [r]
  is 0, we know that [q] has almost reached a power of 2,
  and we increase [p] at the next call, while resetting [r]
  to [q].

  Graphically (numbers are [q], stars are [r]) :

<<
                    10
                  9
                8
              7   *
            6       *
          5           ...
        4
      3   *
    2       *
  1   *       *
0   *   *       *
>>

  We stop when [k], the global downward counter reaches 0.
  At that moment, [q] is the number we're considering (since
  [k+q] is invariant), and [p] its logarithm.
*)

Fixpoint log2_iter k p q r : nat :=
  match k with
  | O    => p
  | S k' =>
    match r with
    | O => log2_iter k' (S p) (S q) q
    | S r' => log2_iter k' p (S q) r'
    end
  end.

Definition log2 n : nat := log2_iter (pred n) 0 1 0.

(** ** Iterator on natural numbers *)

Definition iter (n : nat) {A} (f : A -> A) (x : A) : A :=
  nat_rec A x (fun _ => f) n.

Local Definition ap_S := @ap _ _ S.
Local Definition ap_nat := @ap nat.
#[export] Hint Resolve ap_S : core.
#[export] Hint Resolve ap_nat : core.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  auto.
Defined.

(** Injectivity of successor *)

Definition path_nat_S n m (H : S n = S m) : n = m := ap pred H.
#[export] Hint Immediate path_nat_S : core.

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  auto.
Defined.
#[export] Hint Resolve not_eq_S : core.

(** TODO: keep or remove? *)
Definition IsSucc (n: nat) : Type :=
  match n with
  | O => False
  | S p => True
  end.

(** Zero is not the successor of a number *)

Theorem not_eq_O_S : forall n:nat, 0 <> S n.
Proof.
  discriminate.
Defined.
#[export] Hint Resolve not_eq_O_S : core.

Theorem not_eq_n_Sn : forall n:nat, n <> S n.
Proof.
  induction n; auto.
Defined.
#[export] Hint Resolve not_eq_n_Sn : core.

Local Definition ap011_add := @ap011 _ _ _ add.
Local Definition ap011_nat := @ap011 nat nat.
#[export] Hint Resolve ap011_add : core.
#[export] Hint Resolve ap011_nat : core.

Lemma add_n_O : forall (n : nat), n = n + 0.
Proof.
  induction n; simpl; auto.
Defined.
#[export] Hint Resolve add_n_O : core.

Lemma add_O_n : forall (n : nat), 0 + n = n.
Proof.
  auto.
Defined.

Lemma add_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Defined.
#[export] Hint Resolve add_n_Sm: core.

Lemma add_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  auto.
Defined.

(** Multiplication *)

Local Definition ap011_mul := @ap011 _ _ _  mul.
#[export] Hint Resolve ap011_mul : core.

Lemma mul_n_O : forall n:nat, 0 = n * 0.
Proof.
  induction n; simpl; auto.
Defined.
#[export] Hint Resolve mul_n_O : core.

Lemma mul_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl; auto.
  destruct H; rewrite <- add_n_Sm; apply ap.
  pattern m at 1 3; elim m; simpl; auto.
Defined.
#[export] Hint Resolve mul_n_Sm: core.

(** Standard associated names *)

Notation mul_0_r_reverse := mul_n_O (only parsing).
Notation mul_succ_r_reverse := mul_n_Sm (only parsing).

(** ** Equality of natural numbers *)

(** *** Boolean equality and its properties *)

Fixpoint code_nat (m n : nat) {struct m} : DHProp :=
  match m, n with
  | 0, 0 => True
  | m'.+1, n'.+1 => code_nat m' n'
  | _, _ => False
  end.

Infix "=n" := code_nat : nat_scope.

Fixpoint idcode_nat {n} : (n =n n) :=
  match n as n return (n =n n) with
  | 0 => tt
  | S n' => @idcode_nat n'
  end.

Fixpoint path_nat {n m} : (n =n m) -> (n = m) :=
  match m as m, n as n return (n =n m) -> (n = m) with
  | 0, 0 => fun _ => idpath
  | m'.+1, n'.+1 => fun H : (n' =n m') => ap S (path_nat H)
  | _, _ => fun H => match H with end
  end.

Global Instance isequiv_path_nat {n m} : IsEquiv (@path_nat n m).
Proof.
  refine (isequiv_adjointify
            (@path_nat n m)
            (fun H => transport (fun m' => (n =n m')) H idcode_nat)
            _ _).
  { intros []; simpl.
    induction n; simpl; trivial.
    by destruct (IHn^)%path. }
  { intro. apply path_ishprop. }
Defined.

Definition equiv_path_nat {n m} : (n =n m) <~> (n = m)
  := Build_Equiv _ _ (@path_nat n m) _.

(** Thus [nat] has decidable paths *)
Global Instance decidable_paths_nat : DecidablePaths nat
  := fun n m => decidable_equiv _ (@path_nat n m) _.

(** And is therefore a HSet *)
Global Instance hset_nat : IsHSet nat := _.

(** ** Inequality of natural numbers *)

Inductive leq (n : nat) : nat -> Type :=
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

Lemma leq_n_pred n m : leq n m -> leq (pred n) (pred m).
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
  induction n.
  { intro p.
    inversion p. }
  intros p.
  by apply IHn, leq_S_n.
Defined.

(** A general form for injectivity of this constructor *)
Definition leq_n_inj_gen n k (p : n <= k) (r : n = k) : p = r # leq_n n.
Proof.
  induction p.
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
  induction p.
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
  induction n; auto.
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
  induction m; intros n.
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

Lemma equiv_leq_add n m
  : leq n m <~> exists k, k + n = m.
Proof.
  srapply equiv_iff_hprop.
  { apply hprop_allpath.
    intros [x p] [y q].
    apply path_sigma_hprop.
    simpl.
    revert m p q.
    induction n.
    { intros m p q.
      rewrite <- add_n_O in p,q.
      exact (p @ q^). }
    intros m p q.
    rewrite <- add_n_Sm in p,q.
    destruct m.
    { inversion p. }
    apply path_nat_S in p, q.
    by apply (IHn m). }
  { intros p.
    induction p.
    + exists 0.
      reflexivity.
    + exists IHp.1.+1.
      apply ap_S, IHp.2. }
  intros [k p].
  destruct p.
  apply leq_add.
Defined.

(** We define the less-than relation [lt] in terms of [leq] *)
Definition lt n m : Type := leq (S n) m.
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
  induction n; auto.
  destruct m; auto.
Defined.

(** Maximum and minimum : definitions and specifications *)

Lemma max_n_n n : max n n = n.
Proof.
  induction n; cbn; auto.
Defined.
#[export] Hint Resolve max_n_n : core.

Lemma max_Sn_n n : max (S n) n = S n.
Proof.
  induction n; cbn; auto.
Defined.
#[export] Hint Resolve max_Sn_n : core.

Lemma max_comm n m : max n m = max m n.
Proof.
  revert m; induction n; destruct m; cbn; auto.
Defined.

Lemma max_0_n n : max 0 n = n.
Proof.
  auto.
Defined.
#[export] Hint Resolve max_0_n : core.

Lemma max_n_0 n : max n 0 = n.
Proof.
  by rewrite max_comm.
Defined.
#[export] Hint Resolve max_n_0 : core.

Theorem max_l : forall n m, m <= n -> max n m = n.
Proof.
  intros n m; revert n; induction m; auto.
  intros [] p.
  1: inversion p.
  cbn; by apply ap_S, IHm, leq_S_n.
Defined.

Theorem max_r : forall n m : nat, n <= m -> max n m = m.
Proof.
  intros; rewrite max_comm; by apply max_l.
Defined.

Lemma min_comm : forall n m, min n m = min m n.
Proof.
  induction n; destruct m; cbn; auto.
Defined. 

Theorem min_l : forall n m : nat, n <= m -> min n m = n.
Proof.
  intros n m; revert m; induction n; auto.
  intros [] p.
  1: inversion p.
  cbn; by apply ap_S, IHn, leq_S_n.
Defined.

Theorem min_r : forall n m : nat, m <= n -> min n m = m.
Proof.
  intros; rewrite min_comm; by apply min_l.
Defined.

(** [n]th iteration of the function [f] *)

Fixpoint nat_iter (n:nat) {A} (f:A->A) (x:A) : A :=
  match n with
    | O => x
    | S n' => f (nat_iter n' f x)
  end.

Lemma nat_iter_succ_r n {A} (f:A->A) (x:A) :
  nat_iter (S n) f x = nat_iter n f (f x).
Proof.
  induction n; intros; simpl; rewrite <- ?IHn; trivial.
Defined.

Theorem nat_iter_add :
  forall (n m:nat) {A} (f:A -> A) (x:A),
    nat_iter (n + m) f x = nat_iter n f (nat_iter m f x).
Proof.
  induction n; intros; simpl; rewrite ?IHn; trivial.
Defined.

(** Preservation of invariants : if [f : A -> A] preserves the invariant [Inv], then the iterates of [f] also preserve it. *)

Theorem nat_iter_invariant (n : nat) {A} (f : A -> A) (P : A -> Type)
  : (forall x, P x -> P (f x)) -> forall x, P x -> P (nat_iter n f x).
Proof.
  revert n A f P.
  induction n; simpl; trivial.
  intros A f P Hf x Hx.
  apply Hf, IHn; trivial.
Defined.

(** ** Arithmetic *)

Lemma nat_add_n_O : forall n:nat, n = n + 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; apply ap; assumption.
Defined.

Lemma nat_add_n_Sm : forall n m:nat, (n + m).+1 = n + m.+1.
Proof.
  intros n m; induction n; simpl.
  - reflexivity.
  - apply ap; assumption.
Defined.

Definition nat_add_comm (n m : nat) : n + m = m + n.
Proof.
  revert m; induction n as [|n IH]; intros m; simpl.
  - refine (nat_add_n_O m).
  - transitivity (m + n).+1.
    + apply ap, IH.
    + apply nat_add_n_Sm.
Defined.

(** ** Exponentiation *)

Fixpoint nat_exp (n m : nat) : nat
  := match m with
       | 0 => 1
       | S m => nat_exp n m * n
     end.

(** ** Factorials *)

Fixpoint factorial (n : nat) : nat
  := match n with
       | 0 => 1
       | S n => S n * factorial n
     end.

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
  induction m, n.
  - left; reflexivity.
  - left; apply leq_0_n.
  - right; unfold lt; apply leq_1_Sn.
  - assert ((m <= n) + (n < m)) as X by apply leq_dichot.
    induction X as [leqmn|ltnm].
    + left; apply leq_S_n'; assumption.
    + right; apply leq_S_n'; assumption.
Defined.

Lemma not_lt_n_0 n : ~ (n < 0).
Proof.
  apply not_leq_Sn_0.
Defined.

