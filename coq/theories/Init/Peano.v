(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The type [nat] of Peano natural numbers (built from [O] and [S])
    is defined in [Datatypes.v] *)

(** This module defines the following operations on natural numbers :
    - predecessor [pred]
    - addition [plus]
    - multiplication [mult]
    - less or equal order [le]
    - less [lt]
    - greater or equal [ge]
    - greater [gt]

   It states various lemmas and theorems about natural numbers,
   including Peano's axioms of arithmetic (in Coq, these are provable).
   Case analysis on [nat] and induction on [nat * nat] are provided too
 *)

Require Import Notations.
Require Import Datatypes.
Local Open Scope identity_scope.
Require Import Logic_Type.

Open Scope nat_scope.

Definition eq_S := f_equal S.

Hint Resolve (f_equal S): v62.
Hint Resolve (f_equal (A:=nat)): core.

(** The predecessor function *)

Definition pred (n:nat) : nat := match n with
                                 | O => n
                                 | S u => u
                                 end.
(* Hint Resolve (f_equal pred): v62. *)

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  simpl; reflexivity.
Qed.

(** Injectivity of successor *)

Definition eq_add_S n m (H: S n = S m): n = m := f_equal pred H.
Hint Immediate eq_add_S: core.

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  red; auto.
Qed.
Hint Resolve not_eq_S: core.

Definition IsSucc (n:nat) : Type :=
  match n with
  | O => False
  | S p => True
  end.

(** Zero is not the successor of a number *)

(* XXX Andrej: Try to put back in, does not work with current Coq. *)
(* Theorem O_S : forall n:nat, 0 <> S n. *)
(* Proof. *)
(*   discriminate. *)
(* Qed. *)
(* Hint Resolve O_S: core. *)

(* XXX Andrej: Try to put back in, does not work with current Coq. *)
(* Theorem n_Sn : forall n:nat, n <> S n. *)
(* Proof. *)
(*   induction n; auto. *)
(* Qed. *)
(* Hint Resolve n_Sn: core. *)

(** addition *)

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.

Hint Resolve (f_equal2 plus): v62.
Hint Resolve (f_equal2 (A1:=nat) (A2:=nat)): core.

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve plus_n_O: core.

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof.
  auto.
Qed.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Qed.
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  auto.
Qed.

(** Standard associated names *)

Notation plus_0_r_reverse := plus_n_O (compat "8.2").
Notation plus_succ_r_reverse := plus_n_Sm (compat "8.2").

(** Multiplication *)

Fixpoint mult (n m:nat) : nat :=
  match n with
  | O => 0
  | S p => m + p * m
  end

where "n * m" := (mult n m) : nat_scope.

Hint Resolve (f_equal2 mult): core.

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl; auto.
  destruct H; rewrite <- plus_n_Sm; apply eq_S.
  pattern m at 1 3; elim m; simpl; auto.
Qed.
Hint Resolve mult_n_Sm: core.

(** Standard associated names *)

Notation mult_0_r_reverse := mult_n_O (compat "8.2").
Notation mult_succ_r_reverse := mult_n_Sm (compat "8.2").

(** Truncated subtraction: [m-n] is [0] if [n>=m] *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.

(** Definition of the usual orders, the basic properties of [le] and [lt]
    can be found in files Le and Lt *)

Inductive le (n:nat) : nat -> Type :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Hint Constructors le: core.
(*i equivalent to : "Hints Resolve le_n le_S : core." i*)

Definition lt (n m:nat) := S n <= m.
Hint Unfold lt: core.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
Hint Unfold ge: core.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core.

Infix ">" := gt : nat_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

Theorem le_pred : forall n m, n <= m -> pred n <= pred m.
Proof.
induction 1; auto. destruct m; simpl; auto.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
intros n m. exact (le_pred (S n) (S m)).
Qed.

(** Case analysis *)

Theorem nat_case :
 forall (n:nat) (P:nat -> Type), P 0 -> (forall m:nat, P (S m)) -> P n.
Proof.
  induction n; auto.
Qed.

(** Principle of double induction *)

Theorem nat_double_ind :
 forall R:nat -> nat -> Type,
   (forall n:nat, R 0 n) ->
   (forall n:nat, R (S n) 0) ->
   (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.
Proof.
  induction n; auto.
  destruct m; auto.
Qed.

(** Maximum and minimum : definitions and specifications *)

Fixpoint max n m : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m : nat :=
  match n, m with
    | O, _ => 0
    | S n', O => 0
    | S n', S m' => S (min n' m')
  end.

(* Theorem max_l : forall n m : nat, m <= n -> max n m = n. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

(* Theorem max_r : forall n m : nat, n <= m -> max n m = m. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

(* Theorem min_l : forall n m : nat, n <= m -> min n m = n. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

(* Theorem min_r : forall n m : nat, m <= n -> min n m = m. *)
(* Proof. *)
(* induction n; destruct m; simpl; auto. inversion 1. *)
(* intros. apply f_equal. apply IHn. apply le_S_n. trivial. *)
(* Qed. *)

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
Qed.

Theorem nat_iter_plus :
  forall (n m:nat) {A} (f:A -> A) (x:A),
    nat_iter (n + m) f x = nat_iter n f (nat_iter m f x).
Proof.
  induction n; intros; simpl; rewrite ?IHn; trivial.
Qed.

(** Preservation of invariants : if [f : A->A] preserves the invariant [Inv],
    then the iterates of [f] also preserve it. *)

Theorem nat_iter_invariant :
  forall (n:nat) {A} (f:A -> A) (P : A -> Type),
    (forall x, P x -> P (f x)) ->
    forall x, P x -> P (nat_iter n f x).
Proof.
  induction n; simpl; trivial.
  intros A f P Hf x Hx. apply Hf, IHn; trivial.
Qed.
