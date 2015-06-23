(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers, depending on TruncType *)

Require Import HoTT.Basics.
Require Import HoTT.Types.Bool HoTT.Types.Nat.
Require Import HoTT.TruncType HoTT.DProp.



(** Much of the layout of this file is adapted from ssreflect *)

(** ** Equality *)
(** *** Boolean equality and its properties *)

Fixpoint code_nat (m n : nat) {struct m} : DHProp :=
  match m, n with
    | 0, 0 => True
    | m'.+1, n'.+1 => code_nat m' n'
    | _, _ => False
  end.

Infix "=n" := code_nat (at level 70, no associativity) : nat_scope.

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

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n" := (m.+1 <= n) : nat_scope.
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
