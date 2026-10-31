From HoTT.Basics Require Import Overture Notations.
From HoTT.Spaces Require Import Nat.Core Nat.Arithmetic SInt.

Goal forall n : nat, n = n.
Proof.
  intro n; induction n; reflexivity.
Qed.

Goal forall (A : Type) (n : nat), A -> A.
Proof.
  intros A n a; induction n; exact a.
Qed.

Goal Empty -> Unit.
Proof.
  intro x; elim x.
Qed.

Goal forall A : Type, Empty -> A.
Proof.
  intros A x; elim x.
Qed.

Goal forall n m (p : (n <= m)%nat), p = p.
Proof.
  intros n m p; induction p; reflexivity.
Qed.

Goal forall n m, increasing_geq n m -> Unit.
Proof.
  intros n m p; induction p; exact tt.
Qed.

Goal forall x : SInt, x = x.
Proof.
  intro x; induction x; reflexivity.
Qed.

Goal forall (A : Type) (x : SInt), A -> A.
Proof.
  intros A x a; induction x; exact a.
Qed.
