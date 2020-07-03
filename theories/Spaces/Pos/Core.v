Require Import Basics.

(* ** Binary Positive Integers *)

(** Most of this file has been adapted from the coq standard library for positive binary integers. *)

(** Here we define the inductive type of positive binary numbers. *)
Inductive Pos : Type0 :=
  | xH : Pos
  | x0 : Pos -> Pos
  | x1 : Pos -> Pos.

Declare Scope positive_scope.
Delimit Scope positive_scope with pos.

(** Here are some notations that let us right binary positive integers more easily. *)
Notation "1" := xH : positive_scope.
Notation "p ~ 1" := (x1 p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Notation "p ~ 0" := (x0 p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Local Open Scope positive_scope.

(** ** Successor *)
Fixpoint pos_succ x :=
  match x with
    | p~1 => (pos_succ p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.

(** Peano induction (due to Daniel Schepler) *)
Fixpoint pos_peano_ind (P : Pos -> Type) (a : P 1)
  (f : forall p, P p -> P (pos_succ p)) (p : Pos) : P p
  := let f2 := pos_peano_ind (fun p => P (p~0))
    (f _ a) (fun p (x : P p~0) => f _ (f _ x))
  in match p with
      | q~1 => f _ (f2 q)
      | q~0 => f2 q
      | 1 => a
     end.

(** Computation rules for Peano induction *)
Definition pos_peano_ind_beta_1 (P : Pos -> Type) (a : P 1)
  (f : forall p, P p -> P (pos_succ p))
  : pos_peano_ind P a f 1 = a := idpath.

Definition pos_peano_ind_beta_pos_succ (P : Pos -> Type) (a : P 1)
  (f : forall p, P p -> P (pos_succ p)) (p : Pos)
  : pos_peano_ind P a f (pos_succ p) = f _ (pos_peano_ind P a f p).
Proof.
  revert P a f.
  induction p; trivial.
  intros P a f.
  srapply IHp.
Qed.

Definition pos_peano_rec (P : Type)
  : P -> (Pos -> P -> P) -> Pos -> P
  := pos_peano_ind (fun _ => P).

Definition pos_peano_rec_beta_pos_succ (P : Type)
  (a : P) (f : Pos -> P -> P) (p : Pos)
  : pos_peano_rec P a f (pos_succ p) = f p (pos_peano_rec P a f p)
  := pos_peano_ind_beta_pos_succ (fun _ => P) a f p.

(** ** Properties of constructors *)

Definition x0_inj {z w : Pos} (p : x0 z = x0 w) : z = w
  := transport (fun s => z = (
    match s with xH => w | x0 a => a | x1 a => w end)) p idpath.

Definition x1_inj {z w : Pos} (p : x1 z = x1 w) : z = w
  := transport (fun s => z = (
    match s with xH => w | x0 a => w | x1 a => a end)) p idpath.

Definition x0_neq_xH {z : Pos} : x0 z <> xH
  := fun p => transport (fun s =>
    match s with xH => Empty | x0 a => z = a | x1 a => Empty end) p idpath.

Definition x1_neq_xH {z : Pos} : x1 z <> xH
  := fun p => transport (fun s =>
    match s with xH => Empty | x0 a => Empty | x1 a => z = a end) p idpath.

Definition x0_neq_x1 {z w : Pos} : x0 z <> x1 w
  := fun p => transport (fun s =>
    match s with xH => Empty | x0 a => z = a | x1 _ => Empty end) p idpath.

Definition xH_neq_x0 {z : Pos} : xH <> x0 z
  := x0_neq_xH o symmetry _ _.

Definition xH_neq_x1 {z : Pos} : xH <> x1 z
  := x1_neq_xH o symmetry _ _.

Definition x1_neq_x0 {z w : Pos} : x1 z <> x0 w
  := x0_neq_x1 o symmetry _ _.

(** * Positive binary integers have decidable paths *)

Global Instance decpaths_pos : DecidablePaths Pos.
Proof.
  intros n; induction n as [|zn|on];
  intros m; induction m as [|zm|om].
  + exact (inl idpath).
  + exact (inr xH_neq_x0).
  + exact (inr xH_neq_x1).
  + exact (inr x0_neq_xH).
  + destruct (IHzn zm) as [p|q].
    - apply inl, ap, p.
    - apply inr; intro p.
      by apply q, x0_inj.
  + exact (inr x0_neq_x1).
  + exact (inr x1_neq_xH).
  + exact (inr x1_neq_x0).
  + destruct (IHon om) as [p|q].
    - apply inl, ap, p.
    - apply inr; intro p.
      by apply q, x1_inj.
Defined.

(** Decidable paths imply Pos is a hSet *)
Global Instance ishset_pos : IsHSet Pos := _.

(** * Operations over positive numbers *)

(** ** Addition *)

Fixpoint pos_add x y :=
  match x, y with
    | p~1, q~1 => (pos_add_carry p q)~0
    | p~1, q~0 => (pos_add p q)~1
    | p~1, 1 => (pos_succ p)~0
    | p~0, q~1 => (pos_add p q)~1
    | p~0, q~0 => (pos_add p q)~0
    | p~0, 1 => p~1
    | 1, q~1 => (pos_succ q)~0
    | 1, q~0 => q~1
    | 1, 1 => 1~0
  end

with pos_add_carry x y :=
  match x, y with
    | p~1, q~1 => (pos_add_carry p q)~1
    | p~1, q~0 => (pos_add_carry p q)~0
    | p~1, 1 => (pos_succ p)~1
    | p~0, q~1 => (pos_add_carry p q)~0
    | p~0, q~0 => (pos_add p q)~1
    | p~0, 1 => (pos_succ p)~0
    | 1, q~1 => (pos_succ q)~1
    | 1, q~0 => (pos_succ q)~0
    | 1, 1 => 1~1
  end.

Infix "+" := pos_add : positive_scope.

(** ** Operation [x -> 2*x-1] *)

Fixpoint pos_pred_double x :=
  match x with
    | p~1 => p~0~1
    | p~0 => (pos_pred_double p)~1
    | 1 => 1
  end.

(** ** Predecessor *)

Definition pos_pred x :=
  match x with
    | p~1 => p~0
    | p~0 => pos_pred_double p
    | 1 => 1
  end.

(** ** An auxiliary type for subtraction *)

Inductive Pos_mask : Set :=
  | IsNul : Pos_mask
  | IsPos : Pos -> Pos_mask
  | IsNeg : Pos_mask.

(** ** Operation [x -> 2*x+1] *)

Definition pos_mask_succ_double (x : Pos_mask) : Pos_mask :=
  match x with
    | IsNul => IsPos 1
    | IsNeg => IsNeg
    | IsPos p => IsPos p~1
  end.

(** ** Operation [x -> 2*x] *)

Definition pos_mask_double (x : Pos_mask) : Pos_mask :=
  match x with
    | IsNul => IsNul
    | IsNeg => IsNeg
    | IsPos p => IsPos p~0
  end.

(** ** Operation [x -> 2*x-2] *)

Definition pos_mask_double_pred x : Pos_mask :=
  match x with
    | p~1 => IsPos p~0~0
    | p~0 => IsPos (pos_pred_double p)~0
    | 1 => IsNul
  end.

(** ** Predecessor with mask *)

Definition pos_mask_pred (p : Pos_mask) : Pos_mask :=
  match p with
    | IsPos 1 => IsNul
    | IsPos q => IsPos (pos_pred q)
    | IsNul => IsNeg
    | IsNeg => IsNeg
  end.

(** ** Subtraction, result as a mask *)

Fixpoint pos_mask_sub (x y : Pos) {struct y} : Pos_mask :=
  match x, y with
    | p~1, q~1 => pos_mask_double (pos_mask_sub p q)
    | p~1, q~0 => pos_mask_succ_double (pos_mask_sub p q)
    | p~1, 1 => IsPos p~0
    | p~0, q~1 => pos_mask_succ_double (pos_mask_sub_carry p q)
    | p~0, q~0 => pos_mask_double (pos_mask_sub p q)
    | p~0, 1 => IsPos (pos_pred_double p)
    | 1, 1 => IsNul
    | 1, _ => IsNeg
  end

with pos_mask_sub_carry (x y : Pos) {struct y} : Pos_mask :=
  match x, y with
    | p~1, q~1 => pos_mask_succ_double (pos_mask_sub_carry p q)
    | p~1, q~0 => pos_mask_double (pos_mask_sub p q)
    | p~1, 1 => IsPos (pos_pred_double p)
    | p~0, q~1 => pos_mask_double (pos_mask_sub_carry p q)
    | p~0, q~0 => pos_mask_succ_double (pos_mask_sub_carry p q)
    | p~0, 1 => pos_mask_double_pred p
    | 1, _ => IsNeg
  end.

(** ** Subtraction, result as a positive, returning 1 if [x<=y] *)

Definition pos_sub x y :=
  match pos_mask_sub x y with
    | IsPos z => z
    | _ => 1
  end.

Infix "-" := pos_sub : positive_scope.

(** ** Multiplication *)

Fixpoint pos_mul x y :=
  match x with
    | p~1 => y + (pos_mul p y)~0
    | p~0 => (pos_mul p y)~0
    | 1 => y
  end.

Infix "*" := pos_mul : positive_scope.

(** ** Iteration over a positive number *)

Definition pos_iter {A : Type} (f : A -> A)
  : Pos -> A -> A.
Proof.
  apply (pos_peano_ind (fun _ => A -> A) f).
  intros n g.
  exact (f o g).
Defined.

(** ** Power *)

Definition pos_pow (x : Pos) := pos_iter (pos_mul x) 1.

(* We cannot use this notation because it is reserved for path inverse. *)
(* Infix "^" := pos_pow : positive_scope. *)

(** ** Square *)

Fixpoint pos_square p :=
  match p with
    | p~1 => (pos_square p + p)~0~1
    | p~0 => (pos_square p)~0~0
    | 1 => 1
  end.

(** ** Division by 2 rounded below but for 1 *)

Definition pos_div2 p :=
  match p with
    | 1 => 1
    | p~0 => p
    | p~1 => p
  end.

(** Division by 2 rounded up *)

Definition pos_div2_up p :=
 match p with
   | 1 => 1
   | p~0 => p
   | p~1 => pos_succ p
 end.

(** ** Number of digits in a positive number *)

Fixpoint nat_pos_size p : nat :=
  match p with
    | 1 => S O
    | p~1 => S (nat_pos_size p)
    | p~0 => S (nat_pos_size p)
  end.

(** Same, with positive output *)

Fixpoint pos_size p :=
  match p with
    | 1 => 1
    | p~1 => pos_succ (pos_size p)
    | p~0 => pos_succ (pos_size p)
  end.

(** ** From binary positive numbers to Peano natural numbers *)

Definition pos_iter_op {A} (op : A -> A -> A)
  := fix pos_iter (p : Pos) (a : A) : A
    := match p with
        | 1 => a
        | p~0 => pos_iter p (op a a)
        | p~1 => op a (pos_iter p (op a a))
       end.

(** ** From Peano natural numbers to binary positive numbers *)

(** A version preserving positive numbers, and sending 0 to 1. *)

Fixpoint pos_of_nat (n : nat) : Pos :=
 match n with
   | O => 1
   | S O => 1
   | S x => pos_succ (pos_of_nat x)
 end.

(* Another version that converts [n] into [n+1] *)

Fixpoint pos_of_succ_nat (n : nat) : Pos :=
  match n with
    | O => 1
    | S x => pos_succ (pos_of_succ_nat x)
  end.

(** ** Conversion with a decimal representation for printing/parsing *)

Local Notation ten := 1~0~1~0.

Fixpoint pos_of_uint_acc (d : Decimal.uint) (acc : Pos) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 l => pos_of_uint_acc l (pos_mul ten acc)
  | Decimal.D1 l => pos_of_uint_acc l (pos_add 1 (pos_mul ten acc))
  | Decimal.D2 l => pos_of_uint_acc l (pos_add 1~0 (pos_mul ten acc))
  | Decimal.D3 l => pos_of_uint_acc l (pos_add 1~1 (pos_mul ten acc))
  | Decimal.D4 l => pos_of_uint_acc l (pos_add 1~0~0 (pos_mul ten acc))
  | Decimal.D5 l => pos_of_uint_acc l (pos_add 1~0~1 (pos_mul ten acc))
  | Decimal.D6 l => pos_of_uint_acc l (pos_add 1~1~0 (pos_mul ten acc))
  | Decimal.D7 l => pos_of_uint_acc l (pos_add 1~1~1 (pos_mul ten acc))
  | Decimal.D8 l => pos_of_uint_acc l (pos_add 1~0~0~0 (pos_mul ten acc))
  | Decimal.D9 l => pos_of_uint_acc l (pos_add 1~0~0~1 (pos_mul ten acc))
  end.

Fixpoint pos_of_uint (d : Decimal.uint) : option Pos :=
  match d with
    | Decimal.Nil => None
    | Decimal.D0 l => pos_of_uint l
    | Decimal.D1 l => Some (pos_of_uint_acc l 1)
    | Decimal.D2 l => Some (pos_of_uint_acc l 1~0)
    | Decimal.D3 l => Some (pos_of_uint_acc l 1~1)
    | Decimal.D4 l => Some (pos_of_uint_acc l 1~0~0)
    | Decimal.D5 l => Some (pos_of_uint_acc l 1~0~1)
    | Decimal.D6 l => Some (pos_of_uint_acc l 1~1~0)
    | Decimal.D7 l => Some (pos_of_uint_acc l 1~1~1)
    | Decimal.D8 l => Some (pos_of_uint_acc l 1~0~0~0)
    | Decimal.D9 l => Some (pos_of_uint_acc l 1~0~0~1)
  end.

Definition pos_of_decimal_int (d:Decimal.int) : option Pos :=
  match d with
  | Decimal.Pos d => pos_of_uint d
  | Decimal.Neg _ => None
  end.

Fixpoint pos_to_little_uint p :=
  match p with
  | 1 => Decimal.D1 Decimal.Nil
  | p~1 => Decimal.Little.succ_double (pos_to_little_uint p)
  | p~0 => Decimal.Little.double (pos_to_little_uint p)
  end.

Definition pos_to_uint p := Decimal.rev (pos_to_little_uint p).

Definition pos_to_decimal_int n := Decimal.Pos (pos_to_uint n).

Numeral Notation Pos pos_of_decimal_int pos_to_uint : positive_scope.

