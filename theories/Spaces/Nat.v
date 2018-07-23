(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers, depending on TruncType *)

Require Export Coq.Init.Peano.
Require Import HoTT.Basics.
Require Import HoTT.Types.Bool.
Require Import HoTT.TruncType HoTT.DProp.

(** We reopen these scopes so they take precedence over nat_scope; otherwise, now that we have [Coq.Init.Peano], we'd get [* : nat -> nat -> nat] rather than [* : Type -> Type -> Type]. *)
Global Open Scope type_scope.
Global Open Scope core_scope.

(** But in this file, we want to be able to use the usual symbols for natural number arithmetic. *)
Local Open Scope nat_scope.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.

(** ** Arithmetic *)

Lemma nat_plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; apply ap; assumption.
Qed.

Lemma nat_plus_n_Sm : forall n m:nat, (n + m).+1 = n + m.+1.
Proof.
  intros n m; induction n; simpl.
  - reflexivity.
  - apply ap; assumption.
Qed.

Definition nat_plus_comm (n m : nat) : n + m = m + n.
Proof.
  revert m; induction n as [|n IH]; intros m; simpl.
  - refine (nat_plus_n_O m).
  - transitivity (m + n).+1.
    + apply ap, IH.
    + apply nat_plus_n_Sm.
Qed.

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

(* here ends the old Types/Nat.v and starts Spaces.v *)

(** Much of the layout of this file is adapted from ssreflect *)

(** ** Equality *)
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
  := BuildEquiv _ _ (@path_nat n m) _.

Global Instance decidable_paths_nat : DecidablePaths nat
  := fun n m => decidable_equiv _ (@path_nat n m) _.

Corollary hset_nat : IsHSet nat.
Proof.
  exact _.
Defined.

(** ** Natural number ordering *)

Definition leq m n := ((m - n) =n 0).
Definition lt m n := leq (m.+1) n.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n" := (lt m n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n" := (n < m) (only parsing) : nat_scope.

(** ** Theorems about natural number ordering *)

Fixpoint leq0n {n} : 0 <= n :=
  match n as n return 0 <= n with
    | 0 => tt
    | n'.+1 => @leq0n n'
  end.

Fixpoint subnn {n} : n - n =n 0 :=
  match n as n return n - n =n 0 with
    | 0 => tt
    | n'.+1 => @subnn n'
  end.

Global Instance leq_refl : Reflexive leq
  := @subnn.

Fixpoint leqnSn {n} : n <= S n :=
  match n as n return n <= S n with
  | 0 => tt
  | n'.+1 => @leqnSn n'
  end.

Fixpoint leq_transd {x y z} : (x <= y -> y <= z -> x <= z)%dprop :=
  match x as x, y as y, z as z return (x <= y -> y <= z -> x <= z)%dprop with
    | 0, 0, 0 => dprop_istrue
    | x'.+1, 0, 0 => dprop_istrue
    | 0, y'.+1, 0 => dprop_istrue
    | 0, 0, z'.+1 => dprop_istrue
    | x'.+1, y'.+1, 0 => dprop_istrue
    | x'.+1, 0, z'.+1 => dprop_istrue
    | 0, y'.+1, z'.+1 => @leq_transd 0 y' z'
    | x'.+1, y'.+1, z'.+1 => @leq_transd x' y' z'
  end.

Global Instance leq_trans : Transitive (fun n m => leq n m)
  := @leq_transd.

Fixpoint leq_antisymd {x y} : (x <= y -> y <= x -> x =n y)%dprop :=
  match x as x, y as y return (x <= y -> y <= x -> x =n y)%dprop with
    | 0, 0 => dprop_istrue
    | x'.+1, y'.+1 => @leq_antisymd x' y'
    | _, _ => dprop_istrue
  end.

Lemma leq_antisym : forall {x y}, x <= y -> y <= x -> x = y.
Proof.
  intros x y p q.
  apply path_nat.
  apply leq_antisymd; assumption.
Defined.

Definition not_nltn n : ~ (n < n).
Proof.
  induction n as [|n IH]; simpl.
  - auto.
  - apply IH.
Defined.

Definition leq1Sn {n} : 1 <= n.+1 := tt.

Fixpoint leqdichot {m} {n} : ((m <= n) + (m > n))%type.
Proof.
  induction m, n.
  - left; reflexivity.
  - left; apply leq0n.
  - right; unfold lt; apply leq1Sn.
  - assert ((m <= n) + (n < m)) as X by apply leqdichot.
    induction X as [leqmn|ltnm].
    + left; assumption.
    + right; assumption.
Defined.
