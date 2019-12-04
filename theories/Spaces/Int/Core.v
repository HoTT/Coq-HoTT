Require Import Basics.
Require Import Spaces.Pos.

(** * The Integers. *)

Local Close Scope trunc_scope.
Local Close Scope nat_scope.

Local Open Scope positive_scope.

(** ** Definition of the Integers *)

(** We define an integer as being a positive number labelled negative, zero or a positive number labelled positive. *)
Inductive Int : Type0 :=
  | neg : Pos -> Int
  | zero : Int
  | pos : Pos -> Int.

Declare Scope int_scope.
Local Open Scope int_scope.
Delimit Scope int_scope with int.

(** The integers are a pointed type *)
Global Instance ispointed_Int : IsPointed Int := zero.

(** Properties of constructors *)

Definition neg_inj {z w : Pos} (p : neg z = neg w) : z = w
  := transport (fun s => z =
    (match s with neg a => a | zero => w | pos a => w end)) p (idpath z).

Definition pos_inj {z w : Pos} (p : pos z = pos w) : z = w
  := transport (fun s => z =
    (match s with neg a => w | zero => w | pos a => a end)) p (idpath z).

Definition neg_neq_zero {z : Pos} : ~ (neg z = zero)
  := fun p => transport (fun s =>
    match s with neg a => z = a| zero => Empty | pos _ => Empty end) p (idpath z).

Definition pos_neq_zero {z : Pos} : ~ (pos z = zero)
  := fun p => transport (fun s =>
    match s with pos a => z = a | zero => Empty | neg _ => Empty end) p (idpath z).

Definition neg_neq_pos {z w : Pos} : ~ (neg z = pos w)
  := fun p => transport (fun s =>
    match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (idpath z).

Definition zero_neq_neg {z : Pos} := @neg_neq_zero z o symmetry _ _.

Definition zero_neq_pos {z : Pos} := @pos_neq_zero z o symmetry _ _.

Definition pos_neq_neg {z w : Pos} := @neg_neq_pos z w o symmetry _ _.

(** ** Conversion with a decimal representation for printing/parsing *)

Definition int_to_decimal_int (n : Int) : Decimal.int :=
  match n with
    | neg m => Decimal.Neg (pos_to_uint m)
    | zero  => Decimal.Pos Decimal.Nil
    | pos m => Decimal.Pos (pos_to_uint m)
  end.

Fixpoint int_of_decimal_uint (d : Decimal.uint) : Int :=
  match d with
    | Decimal.Nil => zero
    | Decimal.D0 l => int_of_decimal_uint l
    | Decimal.D1 l => pos (pos_of_uint_acc l 1)
    | Decimal.D2 l => pos (pos_of_uint_acc l 1~0)
    | Decimal.D3 l => pos (pos_of_uint_acc l 1~1)
    | Decimal.D4 l => pos (pos_of_uint_acc l 1~0~0)
    | Decimal.D5 l => pos (pos_of_uint_acc l 1~0~1)
    | Decimal.D6 l => pos (pos_of_uint_acc l 1~1~0)
    | Decimal.D7 l => pos (pos_of_uint_acc l 1~1~1)
    | Decimal.D8 l => pos (pos_of_uint_acc l 1~0~0~0)
    | Decimal.D9 l => pos (pos_of_uint_acc l 1~0~0~1)
  end.

Definition int_of_decimal_int (d : Decimal.int) : Int :=
  match d with
    | Decimal.Pos u => int_of_decimal_uint u
    | Decimal.Neg u => let t := int_of_decimal_uint u in
        match t with
          | pos v => neg v
          | _ => zero
        end
  end.

Numeral Notation Int int_of_decimal_int int_to_decimal_int : int_scope.

(* For some reason 0 can be parsed as an integer, but is printed as [zero]. This notation fixes that. *)
Notation "0" := zero : int_scope.

(** ** Doubling and variants *)

Definition int_double x :=
  match x with
    | 0 => 0
    | pos p => pos p~0
    | neg p => neg p~0
  end.

Definition int_succ_double x :=
  match x with
    | 0 => 1
    | pos p => pos p~1
    | neg p => neg (pos_pred_double p)
  end.

Definition int_pred_double x :=
  match x with
    | 0 => neg 1%pos
    | neg p => neg p~1
    | pos p => pos (pos_pred_double p)
  end.

(** ** Subtraction of positive into Int *)

Fixpoint int_pos_sub (x y : Pos) {struct y} : Int :=
  match x, y with
    | p~1, q~1 => int_double (int_pos_sub p q)
    | p~1, q~0 => int_succ_double (int_pos_sub p q)
    | p~1, 1 => pos p~0
    | p~0, q~1 => int_pred_double (int_pos_sub p q)
    | p~0, q~0 => int_double (int_pos_sub p q)
    | p~0, 1 => pos (pos_pred_double p)
    | 1, q~1 => neg q~0
    | 1, q~0 => neg (pos_pred_double q)
    | 1, 1 => zero
  end%pos.

(** ** Negation *)

Definition int_negation x :=
  match x with
    | zero => zero
    | pos x => neg x
    | neg x => pos x
  end.

Notation "- x" := (int_negation x) : int_scope.

Lemma int_negation_negation n : --n = n.
Proof.
  by destruct n.
Qed.

(** ** Addition *)

Definition int_add x y :=
  match x, y with
    | 0, y => y
    | x, 0 => x
    | pos x', pos y' => pos (x' + y')
    | pos x', neg y' => int_pos_sub x' y'
    | neg x', pos y' => int_pos_sub y' x'
    | neg x', neg y' => neg (x' + y')
  end.

Infix "+" := int_add : int_scope.

(** ** Successor *)

Definition int_succ x := x + 1.

(** ** Predecessor *)

Definition int_pred x := x + neg 1%pos.

(** ** Subtraction *)

Definition int_sub m n := m + -n.

Infix "-" := int_sub : int_scope.

(** ** Multiplication *)

Definition int_mul x y :=
  match x, y with
    | 0, _ => 0
    | _, 0 => 0
    | pos x', pos y' => pos (x' * y')
    | pos x', neg y' => neg (x' * y')
    | neg x', pos y' => neg (x' * y')
    | neg x', neg y' => pos (x' * y')
  end.

Infix "*" := int_mul : int_scope.

(** ** Power function *)

Definition int_pow x y :=
  match y with
    | pos p => pos_iter (int_mul x) p 1
    | 0 => 1
    | neg _ => 0
  end.

Infix "^" := int_pow : int_scope.

(** ** Square *)

Definition int_square x :=
  match x with
    | 0 => 0
    | pos p => pos (pos_square p)
    | neg p => pos (pos_square p)
  end.

(** ** Sign function *)

Definition sgn z :=
  match z with
    | 0 => 0
    | pos p => 1
    | neg p => neg 1%pos
  end.

(* ** Decidable paths and truncation. *)

Global Instance decpaths_int : DecidablePaths Int.
Proof.
  intros [n | | n] [m | | m].
  + destruct (dec (n = m)) as [p | q].
    - apply inl, ap, p.
    - by apply inr; intro; apply q, neg_inj.
  + exact (inr neg_neq_zero).
  + exact (inr neg_neq_pos).
  + exact (inr zero_neq_neg).
  + exact (inl idpath).
  + exact (inr zero_neq_pos).
  + exact (inr pos_neq_neg).
  + exact (inr pos_neq_zero).
  + destruct (dec (n = m)) as [p | q].
    - apply inl, ap, p.
    - by apply inr; intro; apply q, pos_inj.
Defined.

(** Since integers have decidable paths they are a hset *)
Global Instance hset_int : IsHSet Int | 0 := _.
