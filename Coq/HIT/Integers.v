Add LoadPath "..".
Require Import Paths Equivalences HLevel.

(** The natural numbers are an h-set. *)

Theorem nat_decidable : decidable_paths nat.
Proof.
  intros n; induction n.
  intro m; induction m.
  left; auto.
  right. intro H.
  exact (transport (P := fun n => match n with 0 => unit | S _ => Empty_set end) H tt).
  intro m; induction m.
  right. intro H.
  exact (transport (P := fun n => match n with 0 => Empty_set | S _ => unit end) H tt).
  destruct (IHn m) as [p | e].
  left; apply map; assumption.
  right. intro H. apply e.
  exact (transport (P := fun k => n == match k with 0 => n | S l => l end) H (idpath n)).
Defined.

Theorem nat_is_set : is_set nat.
Proof.
  apply decidable_isset.
  apply nat_decidable.
Defined.

(** The integers are a set. *)

Inductive int : Type :=
| pos : nat -> int
| zero : int
| neg : nat -> int.

Theorem int_decidable : decidable_paths int.
Proof.
  intros z; induction z.
  intro z2; induction z2.
  set (ndec := nat_decidable n n0).
  destruct ndec as [p | f].
  left; apply map; assumption.
  right. intro H. apply f.
  exact (transport (P := fun z => n == match z with pos a => a | _ => n end) H (idpath n)).
  right. intro H.
  exact (transport (P := fun z => match z with zero => Empty_set | _ => unit end) H tt).
  right. intro H.
  exact (transport (P := fun z => match z with neg _ => Empty_set | _ => unit end) H tt).
  intro w; induction w.
  right. intro H.
  exact (transport (P := fun z => match z with pos _ => Empty_set | _ => unit end) H tt).
  left; auto.
  right. intro H.
  exact (transport (P := fun z => match z with neg _ => Empty_set | _ => unit end) H tt).
  intro w; induction w.
  right. intro H.
  exact (transport (P := fun z => match z with pos _ => Empty_set | _ => unit end) H tt).
  right. intro H.
  exact (transport (P := fun z => match z with neg _ => unit | _ => Empty_set end) H tt).
  set (ndec := nat_decidable n n0).
  destruct ndec as [p | f].
  left; apply map; assumption.
  right. intro H. apply f.
  exact (transport (P := fun z => n == match z with neg a => a | _ => n end) H (idpath n)).
Defined.

Theorem int_is_set : is_set int.
Proof.
  apply decidable_isset.
  apply int_decidable.
Defined.

(** Successor and predecessor functions. *)

Definition succ (z : int) : int :=
  match z with
    | pos n => pos (S n)
    | zero => pos 0
    | neg 0 => zero
    | neg (S n) => neg n
  end.

Definition pred (z : int) : int :=
  match z with
    | neg n => neg (S n)
    | zero => neg 0
    | pos 0 => zero
    | pos (S n) => pos n
  end.

Definition succ_pred (z : int) :
  succ (pred z) == z.
Proof.
  induction z.
  induction n; auto. auto. auto.
Defined.  

Definition pred_succ (z : int) :
  pred (succ z) == z.
Proof.
  induction z.
  auto. auto. induction n; auto.
Defined.  

Definition succ_equiv : int <~> int.
Proof.
  exists succ.
  apply hequiv_is_equiv with (g := pred).
  apply succ_pred.
  apply pred_succ.
Defined.

(** Addition. *)

Definition zadd : int -> int -> int.
Proof.
  intros z w.
  induction z.
  (* positive *)
  induction n.
  (* 1 *)
  exact (succ w).
  (* >1 *)
  exact (succ IHn).
  (* 0 *)
  exact w.
  (* negative *)
  induction n.
  (* -1 *)
  exact (pred w).
  (* <-1 *)
  exact (pred IHn).
Defined.

Lemma zero_right_unit (z : int) :
  zadd z zero == z.
Proof.
  induction z.
  induction n.
  auto.
  path_via (succ (zadd (pos n) zero)).
  path_via (succ (pos n)).
  auto.
  induction n.
  auto.
  path_via (pred (zadd (neg n) zero)).
  path_via (pred (neg n)).
Defined.
