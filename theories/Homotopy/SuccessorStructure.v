Require Import Basics Types.
Require Import Spaces.Nat.
Require Import Spaces.Int.
Require Import Spaces.Finite.

(** * Successor Structures. *)

(** A successor structure is just a type with a endofunctor on it, called 'successor'. Typical examples include either the integers or natural numbers with the successor (or predecessor) operation. *)

Record SuccStr : Type := {
   ss_carrier : Type ;
   ss_succ : ss_carrier -> ss_carrier ;
}.

Coercion ss_carrier : SuccStr >-> Sortclass.

Declare Scope succ_scope.

Local Open Scope nat_scope.
Local Open Scope succ_scope.

Delimit Scope succ_scope with succ.
Arguments ss_succ {_} _.

Notation "x .+1" := (ss_succ x) : succ_scope.

(** Successor structure of naturals *)
Definition NatSucc : SuccStr := Build_SuccStr nat Nat.succ.

(** Successor structure of integers *)
Definition IntSucc : SuccStr := Build_SuccStr Int int_succ.

Notation "'+N'" := NatSucc (at level 55) : succ_scope.
Notation "'+Z'" := IntSucc (at level 55) : succ_scope.

(** Stratified successor structures *)

Definition StratifiedType (N : SuccStr) (n : nat) : Type := N * Fin n.

Definition stratified_succ (N : SuccStr) (n : nat) (x : StratifiedType N n)
  : StratifiedType N n.
Proof.
  constructor.
  + induction n.
    - induction (snd x).
    - destruct (dec (snd x = inr tt)).
      * exact (ss_succ (fst x)).
      * exact (fst x).
  + exact (fsucc_mod (snd x)).
Defined.

Definition Stratified (N : SuccStr) (n : nat) : SuccStr
  := Build_SuccStr (StratifiedType N n) (stratified_succ N n).

(** Addition in successor structures *)
Fixpoint ss_add {N : SuccStr} (n : N) (k : nat) : N :=
  match k with
  | O   => n
  | S k => (ss_add n k).+1
  end.

Infix "+" := ss_add : succ_scope.

Definition ss_add_succ {N : SuccStr} (n : N) (k : nat)
  : (n + k.+1) = n.+1 + k.
Proof.
  induction k.
  + reflexivity.
  + exact (ap ss_succ IHk).
Defined.

(** Nat and Int segmented by triples *)
Notation "'N3'" := (Stratified (+N) 3) (at level 55) : succ_scope.
Notation "'Z3'" := (Stratified (+Z) 3) (at level 55) : succ_scope.

