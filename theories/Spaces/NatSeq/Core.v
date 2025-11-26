(** * Types of Sequences [nat -> X] *)

From HoTT Require Import Basics Types.
Require Import Spaces.Nat.Core.

Local Open Scope nat_scope.
Local Open Scope type_scope.

(** ** Operations on sequences *)

(** Shift of a sequence by 1 to the left. *)
Definition seq_tail {X : Type} (u : nat -> X) : (nat -> X) := u o S.

(** Add a term to the start of a sequence. *)
Definition seq_cons {X : Type} : X -> (nat -> X) -> (nat -> X).
Proof.
  intros x u [|n].
  - exact x.
  - exact (u n).
Defined.

Definition seq_cons_head_tail {X : Type} (u : nat -> X)
  : seq_cons (u 0) (seq_tail u) == u.
Proof.
  by intros [|n].
Defined.

Definition tail_cons {X : Type} (u : nat -> X) {x : X} : seq_tail (seq_cons x u) == u
  := fun _ => idpath.

(** ** Equivalence relations on sequences.  *)

(** For every [n : nat], we define a relation between two sequences that holds if and only if their first [n] terms are equal. *)
Definition seq_agree_lt {X : Type} (n : nat) (s t : nat -> X) : Type
  := forall (m : nat), m < n -> s m = t m.

(** [seq_agree_lt] has an equivalent inductive definition. We don't use this equivalence, but include it in case it is useful in future work. *)
Definition seq_agree_inductive {X : Type} (n : nat) (s t : nat -> X) : Type.
Proof.
  induction n in s, t |- *.
  - exact Unit.
  - exact ((s 0 = t 0) * (IHn (seq_tail s) (seq_tail t))).
Defined.

Definition seq_agree_inductive_seq_agree_lt {X : Type} {n : nat}
  {s t : nat -> X} (h : seq_agree_lt n s t)
  : seq_agree_inductive n s t.
Proof.
  induction n in s, t, h |- *.
  - exact tt.
  - simpl.
    exact (h 0 _, IHn _ _ (fun m hm => h m.+1 (_ hm))).
Defined.

Definition seq_agree_lt_seq_agree_inductive {X : Type} {n : nat}
  {s t : nat -> X} (h : seq_agree_inductive n s t)
  : seq_agree_lt n s t.
Proof.
  intros m hm.
  induction m in n, s, t, h, hm |- *.
  - revert n hm h; napply gt_zero_ind; intros n h.
    exact (fst h).
  - induction n.
    + contradiction (not_lt_zero_r _ hm).
    + exact (IHm _ (seq_tail s) (seq_tail t) (snd h) _).
Defined.

Definition seq_agree_lt_iff_seq_agree_inductive
  {X : Type} {n : nat} {s t : nat -> X}
  : seq_agree_lt n s t <-> seq_agree_inductive n s t
  := (fun h => seq_agree_inductive_seq_agree_lt h,
      fun h => seq_agree_lt_seq_agree_inductive h).
