From HoTT Require Import Basics.
Require Import Spaces.Pos.Core.

Local Set Universe Minimization ToSet.

(** * Binary Integers *)

Local Close Scope trunc_scope.
Local Close Scope nat_scope.

Local Open Scope positive_scope.

(** ** Definition of the Integers *)

(** We define an integer as being a positive number labelled negative, zero or a positive number labelled positive. *)
Inductive BinInt : Type0 :=
  | neg : Pos -> BinInt
  | zero : BinInt
  | pos : Pos -> BinInt.

Arguments pos p%_pos.

Declare Scope binint_scope.
Local Open Scope binint_scope.
Delimit Scope binint_scope with binint.

(** The integers are a pointed type *)
Instance ispointed_BinInt : IsPointed BinInt := zero.

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

Definition binint_to_decimal_binint (n : BinInt) : Decimal.int :=
  match n with
    | neg m => Decimal.Neg (pos_to_uint m)
    | zero  => Decimal.Pos Decimal.Nil
    | pos m => Decimal.Pos (pos_to_uint m)
  end.

Definition binint_to_number_binint (n : BinInt) : Numeral.int :=
  Numeral.IntDec (binint_to_decimal_binint n).

Fixpoint binint_of_decimal_uint (d : Decimal.uint) : BinInt :=
  match d with
    | Decimal.Nil => zero
    | Decimal.D0 l => binint_of_decimal_uint l
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

Definition binint_of_decimal_binint (d : Decimal.int) : BinInt :=
  match d with
    | Decimal.Pos u => binint_of_decimal_uint u
    | Decimal.Neg u => let t := binint_of_decimal_uint u in
        match t with
          | pos v => neg v
          | _ => zero
        end
  end.

Definition binint_of_number_binint (d:Numeral.int) :=
  match d with
  | Numeral.IntDec d => Some (binint_of_decimal_binint d)
  | Numeral.IntHex _ => None
  end.

Number Notation BinInt binint_of_number_binint binint_to_number_binint : binint_scope.

(* For some reason 0 can be parsed as an integer, but is printed as [zero]. This notation fixes that. *)
Notation "0" := zero : binint_scope.

(** ** Doubling and variants *)

Definition binint_double x :=
  match x with
    | 0 => 0
    | pos p => pos p~0
    | neg p => neg p~0
  end.

Definition binint_succ_double x :=
  match x with
    | 0 => 1
    | pos p => pos p~1
    | neg p => neg (pos_pred_double p)
  end.

Definition binint_pred_double x :=
  match x with
    | 0 => neg 1%pos
    | neg p => neg p~1
    | pos p => pos (pos_pred_double p)
  end.

(** ** Subtraction of positive into [BinInt] *)

Fixpoint binint_pos_sub (x y : Pos) {struct y} : BinInt :=
  match x, y with
    | p~1, q~1 => binint_double (binint_pos_sub p q)
    | p~1, q~0 => binint_succ_double (binint_pos_sub p q)
    | p~1, 1 => pos p~0
    | p~0, q~1 => binint_pred_double (binint_pos_sub p q)
    | p~0, q~0 => binint_double (binint_pos_sub p q)
    | p~0, 1 => pos (pos_pred_double p)
    | 1, q~1 => neg q~0
    | 1, q~0 => neg (pos_pred_double q)
    | 1, 1 => zero
  end%pos.

(** ** Negation *)

Definition binint_negation x :=
  match x with
    | zero => zero
    | pos x => neg x
    | neg x => pos x
  end.

Notation "- x" := (binint_negation x) : binint_scope.

Lemma ibnint_negation_negation n : --n = n.
Proof.
  by destruct n.
Qed.

(** ** Addition *)

Definition binint_add x y :=
  match x, y with
    | 0, y => y
    | x, 0 => x
    | pos x', pos y' => pos (x' + y')
    | pos x', neg y' => binint_pos_sub x' y'
    | neg x', pos y' => binint_pos_sub y' x'
    | neg x', neg y' => neg (x' + y')
  end.

Infix "+" := binint_add : binint_scope.

(** ** Successor *)

Definition binint_succ x := x + 1.

(** ** Predecessor *)

Definition binint_pred x := x + neg 1%pos.

(** ** Subtraction *)

Definition binint_sub m n := m + -n.

Infix "-" := binint_sub : binint_scope.

(** ** Multiplication *)

Definition binint_mul x y :=
  match x, y with
    | 0, _ => 0
    | _, 0 => 0
    | pos x', pos y' => pos (x' * y')
    | pos x', neg y' => neg (x' * y')
    | neg x', pos y' => neg (x' * y')
    | neg x', neg y' => pos (x' * y')
  end.

Infix "*" := binint_mul : binint_scope.

(** ** Power function *)

Definition binint_pow x y :=
  match y with
    | pos p => pos_iter (binint_mul x) p 1
    | 0 => 1
    | neg _ => 0
  end.

(** ** Square *)

Definition binint_square x :=
  match x with
    | 0 => 0
    | pos p => pos (pos_square p)
    | neg p => pos (pos_square p)
  end.

(** ** Sign function *)

Definition binint_sgn z :=
  match z with
    | 0 => 0
    | pos p => 1
    | neg p => neg 1%pos
  end.

(* ** Decidable paths and truncation. *)

Instance decpaths_binint : DecidablePaths BinInt.
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
Instance hset_binint : IsHSet BinInt | 0 := _.
