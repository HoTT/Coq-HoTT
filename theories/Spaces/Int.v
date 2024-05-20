Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable Basics.Equivalences.
Require Basics.Numerals.Decimal.
Require Import Spaces.Nat.Core.

Unset Elimination Schemes.
Set Universe Minimization ToSet.
Set Cumulativity Weak Constraints.

Declare Scope int_scope.

(** * The Integers *)

(** ** Definition *)

(** We define the integers as two copies of [nat] stuck together. This allows us to reuse many lemmas about arithmetic in nat to prove similar lemmas about integers. *)

Inductive Int : Type0 :=
| pos :> nat -> Int
| negS : nat -> Int.

(** ** Number Notations *)

(** Printing *)
Definition int_to_number_int (n : Int) : Numeral.int :=
  match n with
  | pos n => Numeral.IntDec (Decimal.Pos (Nat.to_uint n))
  | negS n => Numeral.IntDec (Decimal.Neg (Nat.to_uint (S n)))
  end.

(** Parsing *)
Definition int_of_number_int (d : Numeral.int) :=
  match d with
  | Numeral.IntDec (Decimal.Pos d) => pos (Nat.of_uint d)
  | Numeral.IntDec (Decimal.Neg d) => negS (pred (Nat.of_uint d))
  | Numeral.IntHex (Hexadecimal.Pos u) => pos (Nat.of_hex_uint u)
  | Numeral.IntHex (Hexadecimal.Neg u) => negS (pred (Nat.of_hex_uint u))
  end.

Number Notation Int int_of_number_int int_to_number_int : int_scope.

Delimit Scope int_scope with int.
Local Open Scope int_scope.

(** Sucessor, Predecessor and Negation *)

(** These operations will be used in the induction principle we derive for [Int] so we need to define them early on. *)

(** *** Successor and Predecessor *)

Definition int_succ (n : Int) : Int :=
  match n with
  | pos n => pos (S n)
  | negS 0 => pos 0
  | negS (S n) => negS n
  end.

Notation "n .+1" := (int_succ n) : int_scope.

Definition int_pred (n : Int) : Int :=
  match n with
  | pos 0 => negS 0
  | pos (S n) => pos n
  | negS n => negS (S n)
  end.

Notation "n .-1" := (int_pred n) : int_scope.

(** *** Negation *)

(** We define negation of integers by cases on the signs of the integers. *)
Definition int_neg@{} (x : Int) : Int :=
  match x with
  | pos 0 => pos 0
  | pos x.+1 => negS x
  | negS x => pos x.+1
  end.

Notation "- x" := (int_neg x) : int_scope.

(** ** Basic Properties *)

(** The integers have decidable equality. *)
Global Instance decidable_paths_int@{} : DecidablePaths Int.
Proof.
  intros x y.
  destruct x as [x | x], y as [y | y].
  2,3: right; intros; discriminate.
  1,2: nrapply decidable_iff.
  1,4: nrapply ap.
  1,3: intros H; by injection H.
  1,2: exact _.
Defined.

(** By Hedberg's theorem, we have that the integers are a set. *)
Global Instance ishset_int@{} : IsHSet Int := _.

(** *** Integer induction *)

(** The induction principle for integers is similar to the induction principle for natural numbers. However we have two induction hypotheses going in either direction starting from 0. *)
Definition Int_ind@{i} (P : Int -> Type@{i})
  (H0 : P (pos 0))
  (HP : forall n : nat, P n -> P (int_succ n))
  (HN : forall n : nat, P (- n) -> P (int_pred (-n)))
  : forall x, P x.
Proof.
  intros [x | x].
  - induction x as [|x IHx] using Core.nat_ind.
    + apply H0.
    + apply (HP x), IHx.
  - induction x as [|x IHx] using Core.nat_ind.
    + apply (HN 0), H0.
    + change (P (int_pred (- x.+1))).
      apply HN, IHx. 
Defined.

(** We record these so that they can be used with the [induction] tactic. *)
Definition Int_rect := Int_ind.
Definition Int_rec := Int_ind.

(** ** Operations *)

(** *** Addition *)

(** Addition for integers is defined by integer inductionn on the first argument. *)
Definition int_add@{} (x y : Int) : Int.
Proof.
  induction x as [|x IHx|x IHx] in y |- *.
  (** [0 + y = y] *)
  - exact y.
  (** [x.+1 + y = (x + y).+1] *)
  - exact (int_succ (IHx y)).
  (** [x.-1 + y = (x + y).-1] *)
  - exact (int_pred (IHx y)).
Defined.

Infix "+" := int_add : int_scope.
Infix "-" := (fun x y => x + -y) : int_scope.

(** *** Multiplication *)

(** Multiplication for integers is defined by integer induction on the first argument. *)
Definition int_mul@{} (x y : Int) : Int.
Proof.
  induction x as [|x IHx|x IHx] in y |- *.
  (** [0 * y = 0] *)
  - exact 0.
  (** [x.+1 * y = y + x * y] *)
  - exact (y + IHx y).
  (** [x.-1 * y = -y + x * y] *)
  - exact (-y + IHx y).
Defined.

Infix "*" := int_mul : int_scope.

(** ** Properties of Operations *)

(** *** Negation *)

(** Negation is involutive. *)
Definition int_neg_neg@{} (x : Int) : - - x = x.  
Proof.
  by induction x as [ | x IHx | [ ] ].
Defined.

(** Negation is an equivalence. *)
Global Instance isequiv_int_neg@{} : IsEquiv int_neg.
Proof.
  snrapply (isequiv_adjointify int_neg int_neg).
  1,2: nrapply int_neg_neg.
Defined.

(** Negation is injective. *)
Definition isinj_int_neg@{} (x y : Int) : - x = - y -> x = y.
Proof.
  apply (equiv_inj int_neg).
Defined.

(** The negation of a successor is the predecessor of the negation. *)
Definition int_neg_succ (x : Int) : - x.+1 = (- x).-1.
Proof.
  by induction x as [|x IHx|[] IHx].
Defined.

(** The negation of a predecessor is the successor of the negation. *)
Definition int_neg_pred (x : Int) : - x.-1 = (- x).+1.
Proof.
  by induction x as [|x IHx|[] IHx].
Defined.

(** The successor of a predecessor is the identity. *)
Definition int_pred_succ@{} (x : Int) : x.-1.+1 = x.
Proof.
  by induction x as [|x IHx|[] IHx].
Defined. 

(** The predecessor of a successor is the identity. *)
Definition int_succ_pred@{} (x : Int) : x.+1.-1 = x.
Proof.
  by induction x as [|x IHx|[] IHx].
Defined.

(** The sucessor is an equivalence on [Int] *)
Global Instance isequiv_int_succ@{} : IsEquiv int_succ
  := isequiv_adjointify int_succ int_pred int_pred_succ int_succ_pred.

(** The predecessor is an equivalence on [Int] *)
Global Instance isequiv_int_pred@{} : IsEquiv int_pred
  := isequiv_inverse int_succ.

(** *** Addition *)

(** Integer addition with zero on the left is the identity by definition. *)
Definition int_add_0_l@{} (x : Int) : 0 + x = x.
Proof.
  reflexivity.
Defined.

(** Integer addition with zero on the right is the identity. *)
Definition int_add_0_r@{} (x : Int) : x + 0 = x.
Proof.
  induction x as [|x IHx|x IHx].
  - reflexivity.
  - change ((x + 0).+1 = x.+1).
    by rewrite IHx.
  - destruct x.
    1: reflexivity.
    change (?x.-1 + ?y) with (x + y).-1.
    by rewrite IHx.
Defined. 

(** Adding a successor on the left is the successor of the sum. *)
Definition int_add_succ_l@{} (x y : Int) : x.+1 + y = (x + y).+1.
Proof.
  induction x as [|x IHx|[] IHx] in y |- *.
  - reflexivity.
  - reflexivity.
  - simpl.
    by rewrite int_pred_succ.
  - simpl. by rewrite !int_pred_succ.
Defined.

(** Adding a predecessor on the left is the predecessor of the sum. *)
Definition int_add_pred_l@{} (x y : Int) : x.-1 + y = (x + y).-1.
Proof.
  induction x as [|x IHx|[] IHx] in y |- *.
  - reflexivity.
  - simpl.
    by rewrite int_succ_pred. 
  - reflexivity.
  - simpl.
    reflexivity.
Defined.

(** Adding a successor on the right is the successor of the sum. *)
Definition int_add_succ_r@{} (x y : Int) : x + y.+1 = (x + y).+1.
Proof.
  induction x as [|x IHx|[] IHx] in y |- *.
  - reflexivity.
  - by rewrite 2 int_add_succ_l, IHx.
  - cbn. 
    by rewrite int_succ_pred, int_pred_succ.
  - change ((- (n.+1)).-1 + y.+1 = ((- (n.+1)).-1 + y).+1).
    rewrite int_add_pred_l.
    rewrite IHx.
    rewrite <- 2 int_add_succ_l.
    rewrite <- int_add_pred_l.
    by rewrite int_pred_succ, int_succ_pred.
Defined.

(** Adding a predecessor on the right is the predecessor of the sum. *)
Definition int_add_pred_r (x y : Int) : x + y.-1 = (x + y).-1.
Proof.
  induction x as [|x IHx|[] IHx] in y |- *.
  - reflexivity.
  - rewrite 2 int_add_succ_l.
    rewrite IHx.
    by rewrite int_pred_succ, int_succ_pred.
  - reflexivity.
  - rewrite 2 int_add_pred_l.
    by rewrite IHx.
Defined.

(** Integer addition is commutative. *)
Definition int_add_comm@{} (x y : Int) : x + y = y + x.
Proof.
  induction y as [|y IHy|y IHy] in x |- *.
  (** [x + 0 = 0 + x] *)
  - apply int_add_0_r.
  (** [x + y.+1 = y.+1 + x] *)
  - change (x + y.+1 = (y + x).+1).
    rewrite <- IHy.
    by rewrite int_add_succ_r.
  - rewrite int_add_pred_r.
    rewrite int_add_pred_l.
    f_ap.
Defined.

(** Integer addition is associative. *)
Definition int_add_assoc@{} (x y z : Int) : x + (y + z) = x + y + z.
Proof.
  induction x as [|x IHx|x IHx] in y, z |- *.
  - reflexivity.
  - change ((x + (y + z)).+1 = (x + y).+1 + z).
    by rewrite int_add_succ_l, IHx.
  - destruct x.
    + cbn.
      by rewrite int_add_pred_l.
    + cbn -[int_add].
      change ((-x.+1 + (y + z)).-1 = (-x.+1).-1 + y + z).
      by rewrite 2 int_add_pred_l, IHx.
Defined.

(** Negation is a left inverse with respect to integer addition. *)
Definition int_add_neg_l@{} (x : Int) : - x + x = 0.
Proof.
  induction x as [|x IHx|x IHx].
  - reflexivity.
  - destruct x.
    + reflexivity.
    + change (((- x.+1).-1 + x.+1.+1) = 0).
      by rewrite int_add_pred_l, int_add_succ_r, IHx.
  - destruct x.
    + reflexivity.
    + change ((- (- (x.+1))).+1 + (- (x.+1)).-1 = 0).
      by rewrite int_neg_neg, int_add_succ_l, int_add_pred_r, IHx.
Defined.

(** Negation is a right inverse with respect to integer addition. *)
Definition int_add_neg_r@{} (x : Int) : x - x = 0.
Proof.
  unfold "-"; by rewrite int_add_comm, int_add_neg_l.
Defined.

(** Negation distributes over addition. *)
Definition int_neg_add@{} (x y : Int) : - (x + y) = - x - y.
Proof.
  induction x as [|x IHx|x IHx] in y |- *.
  - reflexivity.
  - rewrite int_add_succ_l.
    rewrite 2 int_neg_succ.
    rewrite int_add_pred_l.
    f_ap.
  - rewrite int_neg_pred.
    rewrite int_add_succ_l.
    rewrite int_add_pred_l.
    rewrite int_neg_pred.
    f_ap.
Defined.
      
(** *** Multiplication *)

Definition int_mul_succ_l@{} (x y : Int) : x.+1 * y = y + x * y.
Proof.
  induction x as [|x IHx|[] IHx] in y |- *.
  - reflexivity.
  - reflexivity.
  - cbn.
    rewrite int_add_0_r.
    by rewrite int_add_neg_r.
  - rewrite int_pred_succ.
    cbn.
    rewrite int_add_assoc.
    rewrite int_add_neg_r.
    by rewrite int_add_0_l.
Defined.

Definition int_mul_pred_l@{} (x y : Int) : x.-1 * y = -y + x * y.
Proof.
  induction x as [|x IHx|[] IHx] in y |- *.
  - reflexivity.
  - rewrite int_mul_succ_l.
    rewrite int_succ_pred.
    rewrite int_add_assoc.
    by rewrite int_add_neg_l.
  - reflexivity.
  - reflexivity.
Defined.

(** Integer multiplication with zero on the left is zero by definition. *)
Definition int_mul_0_l@{} (x : Int) : 0 * x = 0.
Proof.
  reflexivity.
Defined.

(** Integer multiplication with zero on the right is zero. *)
Definition int_mul_0_r@{} (x : Int) : x * 0 = 0.
Proof.
  induction x as [|x IHx|[|x] IHx].
  - reflexivity.
  - change (0 + x * 0 = 0).
    by rewrite int_add_0_l.
  - reflexivity.
  - rewrite int_mul_pred_l.
    rewrite int_add_0_l.
    by rewrite IHx.
Defined.

Definition int_mul_1_l@{} (x : Int) : 1 * x = x.
Proof.
  apply int_add_0_r.
Defined.

Definition int_mul_1_r@{} (x : Int) : x * 1 = x.
Proof.
  induction x as [|x IHx|[|x] IHx].
  - reflexivity.
  - change (1 + x * 1 = x.+1).
    by rewrite IHx.
  - reflexivity.
  - change ((- (x.+1)).-1 * 1 = (- (x.+1)).-1).
    rewrite int_mul_pred_l.
    by rewrite IHx.
Defined. 

(** Multiplying with a negation on the left is the same as negating the product. *)
Definition int_mul_neg_l@{} (x y : Int) : - x * y = - (x * y).
Proof.
  induction x as [|x IHx|x IHx] in y |- *.
  - reflexivity.
  - rewrite int_neg_succ.
    rewrite int_mul_pred_l.
    rewrite int_mul_succ_l.
    rewrite int_neg_add.
    by rewrite IHx.
  - rewrite int_neg_pred.
    rewrite int_mul_succ_l.
    rewrite int_mul_pred_l.
    rewrite int_neg_add.
    rewrite IHx.
    by rewrite int_neg_neg.
Defined.

Definition int_mul_succ_r@{} (x y : Int) : x * y.+1 = x + x * y.
Proof.
  induction x as [|x IHx|x IHx] in y |- *.
  - reflexivity.
  - rewrite 2 int_mul_succ_l.
    rewrite 2 int_add_succ_l.
    f_ap.
    rewrite IHx.
    rewrite !int_add_assoc; f_ap.
    by rewrite int_add_comm.
  - rewrite 2 int_mul_pred_l.
    rewrite int_neg_succ.
    rewrite int_mul_neg_l.
    rewrite 2 int_add_pred_l.
    f_ap.
    rewrite <- int_mul_neg_l.
    rewrite IHx.
    rewrite !int_add_assoc; f_ap.
    by rewrite int_add_comm.
Defined.

Definition int_mul_pred_r@{} (x y : Int) : x * y.-1 = -x + x * y.
Proof.
  induction x as [|x IHx|x IHx] in y |- *.
  - reflexivity.
  - rewrite 2 int_mul_succ_l.
    rewrite IHx.
    rewrite !int_add_assoc; f_ap.
    rewrite <- (int_neg_neg y.-1).
    rewrite <- int_neg_add.
    rewrite int_neg_pred.
    rewrite int_add_succ_l.
    rewrite int_add_comm.
    rewrite <- int_add_succ_l.
    rewrite int_neg_add.
    by rewrite int_neg_neg.
  - rewrite int_neg_pred.
    rewrite int_neg_neg.
    rewrite 2 int_mul_pred_l.
    rewrite IHx.
    rewrite !int_add_assoc; f_ap.
    rewrite int_neg_pred.
    rewrite int_neg_neg.
    rewrite 2 int_add_succ_l; f_ap.
    by rewrite int_add_comm.
Defined.

(** Integer multiplication is commutative. *)
Definition int_mul_comm@{} (x y : Int) : x * y = y * x.
Proof.
  induction y as [|y IHy|y IHy] in x |- *.
  - apply int_mul_0_r.
  - rewrite int_mul_succ_l.
    rewrite int_mul_succ_r.
    by rewrite IHy.
  - rewrite int_mul_pred_l.
    rewrite int_mul_pred_r.
    by rewrite IHy.
Defined.

(** Multiplying with a negation on the right is the same as negating the product. *)
Definition int_mul_neg_r@{} (x y : Int) : x * - y = - (x * y).
Proof.
  rewrite !(int_mul_comm x).
  apply int_mul_neg_l.
Defined.

(** Multiplication distributes over addition on the left. *)
Definition int_dist_l@{} (x y z : Int) : x * (y + z) = x * y + x * z.
Proof.
  induction x as [|x IHx|x IHx] in y, z |- *.
  - reflexivity.
  - rewrite 3 int_mul_succ_l.
    rewrite IHx.
    rewrite !int_add_assoc; f_ap.
    rewrite <- !int_add_assoc; f_ap.
    by rewrite int_add_comm.
  - rewrite 3 int_mul_pred_l.
    rewrite IHx.
    rewrite !int_add_assoc; f_ap.
    rewrite int_neg_add.
    rewrite <- !int_add_assoc; f_ap.
    by rewrite int_add_comm.
Defined.

(** Multiplication distributes over addition on the right. *)
Definition int_dist_r@{} (x y z : Int) : (x + y) * z = x * z + y * z.
Proof.
  by rewrite int_mul_comm, int_dist_l, !(int_mul_comm z).
Defined.

(** Multiplication is associative. *)
Definition int_mul_assoc@{} (x y z : Int) : x * (y * z) = x * y * z.
Proof.
  induction x as [|x IHx|x IHx] in y, z |- *.
  - reflexivity.
  - rewrite 2 int_mul_succ_l.
    rewrite int_dist_r.
    by rewrite IHx.
  - rewrite 2 int_mul_pred_l.
    rewrite int_dist_r.
    rewrite <- int_mul_neg_l.
    by rewrite IHx.
Defined.
