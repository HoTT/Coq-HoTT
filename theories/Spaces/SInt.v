Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable.
Require Import Basics.Numerals.Decimal Basics.Numeral.
Require Import Spaces.Nat.Core.

Unset Elimination Schemes.
Set Universe Minimization ToSet.

(** * The signed integers *)

(** In this file, we give a simple inductive type that represents the integers.  It is straightforward to show that this type has decidable equality and is therefore a set, and it is also straightforward to print and parse integers using this type.  However, we only use it for these purposes, and treat the HIT integers as our main definition of the integers, since they have an induction principle with better computational behaviour. *)

(** ** Definition *)

(** We define the signed integers as two copies of [nat] glued together around a [zero].  [sint_NegS n] represents [-(n + 1)] and [sint_PosS n] represents [n+1].  The trailing "S" indicates the successor. *)
Inductive SInt : Type0 :=
| sint_NegS : nat -> SInt
| sint_zero : SInt
| sint_PosS : nat -> SInt.

(** We can convert a [nat] to an [SInt] by mapping [0] to [sint_zero] and [S n] to [sint_PosS n]. *)
Definition sint_of_nat (n : nat) : SInt :=
  match n with
  | O => sint_zero
  | S n => sint_PosS n
  end.

(** Symmetrically, we can send [n] to "-n" in this way: *)
Definition negsint_of_nat (n : nat) : SInt :=
  match n with
  | O => sint_zero
  | S n => sint_NegS n
  end.

(** ** Parsing and printing *)

(** Here we define some printing and parsing functions that convert the integers between numeral representations.  We don't register these, but they are used for printing and parsing of the HIT integers in Int.v. *)

(** Printing *)
Definition sint_to_number_int (n : SInt) : Numeral.int :=
  match n with
  | sint_PosS m => IntDec (Pos (to_uint (S m)))
  | sint_zero => IntDec (Pos (to_uint 0))
  | sint_NegS m => IntDec (Neg (to_uint (S m)))
  end.

(** Parsing *)
Definition sint_of_number_int (d : Numeral.int) : SInt :=
  match d with
  | IntDec (Pos u) => sint_of_nat (of_uint u)
  | IntDec (Neg u) => negsint_of_nat (of_uint u)
  | IntHex (Hexadecimal.Pos u) => sint_of_nat (of_hex_uint u)
  | IntHex (Hexadecimal.Neg u) => negsint_of_nat (of_hex_uint u)
  end.

(** ** Successor, predecessor and negation *)

Definition sint_succ (n : SInt) : SInt :=
  match n with
  | sint_PosS n => sint_PosS (S n)
  | sint_zero => sint_PosS 0
  | sint_NegS n => negsint_of_nat n
  end.

Definition sint_pred (n : SInt) : SInt :=
  match n with
  | sint_PosS n => sint_of_nat n
  | sint_zero => sint_NegS 0
  | sint_NegS n => sint_NegS (S n)
  end.

Definition sint_neg@{} (x : SInt) : SInt :=
  match x with
  | sint_PosS x => sint_NegS x
  | sint_zero => sint_zero
  | sint_NegS x => sint_PosS x
  end.

(** The successor of a predecessor is the identity. *)
Definition sint_succ_pred@{} (x : SInt) : sint_succ (sint_pred x) = x.
Proof.
  by destruct x as [ | | []].
Defined.

(** The predecessor of a successor is the identity. *)
Definition sint_pred_succ@{} (x : SInt) : sint_pred (sint_succ x) = x.
Proof.
  by destruct x as [[] | | ].
Defined.

(** ** Decidable Equality *)

(** The signed integers have decidable equality. *)
Instance decidablepaths_sint@{} : DecidablePaths SInt.
Proof.
  intros [x | | x] [y | | y].
  2-4,6-8: right; intros; discriminate.
  2: by left.
  1,2: napply decidable_iff.
  1,3: split.
  1,3: napply ap.
  1,2: intros H; by injection H.
  1,2: exact _. (* Uses decidable equality of [nat]. *)
Defined.

(** By Hedberg's theorem, we have that the signed integers are a set. *)
Instance ishset_sint@{} : IsHSet SInt := _.

(** ** Signed integer induction *)

(** The induction principle for signed integers is similar to the induction principle for natural numbers. However we have two induction hypotheses going in either direction starting from [0].  This is used only in Int.v. *)
Definition SInt_ind@{i} (P : SInt -> Type@{i})
  (H0 : P sint_zero)
  (HP : forall n : nat, P (sint_of_nat n) -> P (sint_PosS n))
  (HN : forall n : nat, P (sint_neg (sint_of_nat n)) -> P (sint_NegS n))
  : forall x, P x.
Proof.
  intros [x | | x].
  - induction x as [|x IHx].
    + apply (HN 0%nat), H0.
    + apply (HN x.+1%nat), IHx.
  - exact H0.
  - induction x as [|x IHx].
    + apply (HP 0%nat), H0.
    + apply (HP x.+1%nat), IHx.
Defined.

(** We record these so that they can be used with the [induction] tactic. *)
Definition SInt_rect := SInt_ind.
Definition SInt_rec := SInt_ind.
