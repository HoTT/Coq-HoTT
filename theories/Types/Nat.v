(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers *)

Require Export Coq.Init.Peano.
Require Import HoTT.Basics.
Require Import HoTT.Types.Bool.

(** We reopen these scopes so they take precedence over nat_scope; otherwise, now that we have [Coq.Init.Peano], we'd get [* : nat -> nat -> nat] rather than [* : Type -> Type -> Type]. *)
Global Open Scope type_scope.
Global Open Scope core_scope.

Local Open Scope equiv_scope.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.

(** Much of the layout of this file is adapted from ssreflect *)

(** ** Equality *)
(** *** Boolean equality and its properties *)

Fixpoint code_nat (m n : nat) {struct m} :=
  match m, n with
    | 0, 0 => true
    | m'.+1, n'.+1 => code_nat m' n'
    | _, _ => false
  end.

Infix "=n" := code_nat (at level 70, no associativity) : nat_scope.

Fixpoint idcode_nat {n} : (n =n n) = true :=
  match n as n return (n =n n) = true with
    | 0 => idpath
    | S n' => @idcode_nat n'
  end.

Fixpoint path_nat {n m} : (n =n m) = true -> n = m :=
  match m as m, n as n return (n =n m) = true -> n = m with
    | 0, 0 => fun _ => idpath
    | m'.+1, n'.+1 => fun H : (n' =n m') = true => ap S (path_nat H)
    | _, _ => fun H => match false_ne_true H with end
  end.

Global Instance isequiv_path_nat {n m} : IsEquiv (@path_nat n m).
Proof.
  refine (isequiv_adjointify
            (@path_nat n m)
            (fun H => transport (fun m' => (n =n m') = true) H idcode_nat)
            _ _).
  { intros []; simpl.
    induction n; simpl; trivial.
    by destruct (IHn^)%path. }
  { intro. apply path_ishprop. }
Defined.

Definition equiv_path_nat {n m} : ((n =n m) = true) <~> (n = m)
  := BuildEquiv _ _ (@path_nat n m) _.

Global Instance decidable_paths_nat : DecidablePaths nat
  := fun n m => @decidable_equiv _ _ (@path_nat n m) _ _.

Corollary hset_nat : IsHSet nat.
Proof.
  exact _.
Defined.

(** ** Natural number ordering *)

Definition leq m n := m - n =n 0.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n" := (m.+1 <= n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n" := (n < m) (only parsing) : nat_scope.
