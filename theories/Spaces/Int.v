Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable Basics.Equivalences Basics.PathGroupoids Types.Paths Types.Universe.
Require Basics.Numerals.Decimal.
Require Import Spaces.Nat.Core.

Unset Elimination Schemes.
Set Universe Minimization ToSet.

Declare Scope int_scope.
Delimit Scope int_scope with int.
Local Open Scope int_scope.

(** * The Integers *)

(** ** Definition *)

(** We define the integers as two copies of [nat] stuck together around a [zero]. *)
Inductive Int : Type0 :=
| negS : nat -> Int
| zero : Int
| posS : nat -> Int.

(** We can convert a [nat] to an [Int] by mapping [0] to [zero] and [S n] to [posS n]. Various operations on [nat] are preserved by this function. See the section on conversion functions starting with [int_nat_succ]. *)
Definition int_of_nat (n : nat) :=
  match n with
  | O => zero
  | S n => posS n
  end.

(** We declare this conversion as a coercion so we can freely use [nat]s in statements about integers. *)
Coercion int_of_nat : nat >-> Int.

(** ** Number Notations *)

(** Here we define some printing and parsing functions that convert the integers between numeral representations so that we can use notations such as [123] for [posS 122] and [-123] for [negS 122]. *)

(** Printing *)
Definition int_to_number_int (n : Int) : Numeral.int :=
  match n with
  | posS n => Numeral.IntDec (Decimal.Pos (Nat.to_uint (S n)))
  | zero => Numeral.IntDec (Decimal.Pos (Nat.to_uint 0))
  | negS n => Numeral.IntDec (Decimal.Neg (Nat.to_uint (S n)))
  end.

(** Parsing *)
Definition int_of_number_int (d : Numeral.int) :=
  match d with
  | Numeral.IntDec (Decimal.Pos d) => int_of_nat (Nat.of_uint d)
  | Numeral.IntDec (Decimal.Neg d) => negS (nat_pred (Nat.of_uint d))
  | Numeral.IntHex (Hexadecimal.Pos u) => int_of_nat (Nat.of_hex_uint u)
  | Numeral.IntHex (Hexadecimal.Neg u) => negS (nat_pred (Nat.of_hex_uint u))
  end.

Number Notation Int int_of_number_int int_to_number_int : int_scope.

(** ** Successor, Predecessor and Negation *)

(** These operations will be used in the induction principle we derive for [Int] so we need to define them early on. *)

(** *** Successor and Predecessor *)

Definition int_succ (n : Int) : Int :=
  match n with
  | posS n => posS (S n)
  | 0 => 1
  | -1 => 0
  | negS (S n) => negS n
  end.

Notation "n .+1" := (int_succ n) : int_scope.

Definition int_pred (n : Int) : Int :=
  match n with
  | posS (S n) => posS n
  | 1 => 0 
  | 0 => -1
  | negS n => negS (S n)
  end.

Notation "n .-1" := (int_pred n) : int_scope.

(** *** Negation *)

Definition int_neg@{} (x : Int) : Int :=
  match x with
  | posS x => negS x
  | zero => zero
  | negS x => posS x
  end.

Notation "- x" := (int_neg x) : int_scope.

(** ** Basic Properties *)

(** *** Integer induction *)

(** The induction principle for integers is similar to the induction principle for natural numbers. However we have two induction hypotheses going in either direction starting from 0. *)
Definition Int_ind@{i} (P : Int -> Type@{i})
  (H0 : P 0)
  (HP : forall n : nat, P n -> P (int_succ n))
  (HN : forall n : nat, P (- n) -> P (int_pred (-n)))
  : forall x, P x.
Proof.
  intros[x | | x].
  - induction x as [|x IHx].
    + apply (HN 0%nat), H0.
    + apply (HN x.+1%nat), IHx.
  - exact H0.
  - induction x as [|x IHx].
    * apply (HP 0%nat), H0.
    * apply (HP x.+1%nat), IHx.
Defined.

(** We record these so that they can be used with the [induction] tactic. *)
Definition Int_rect := Int_ind.
Definition Int_rec := Int_ind.

(** *** Decidable Equality *)

(** The integers have decidable equality. *)
Global Instance decidable_paths_int@{} : DecidablePaths Int.
Proof.
  intros x y.
  destruct x as [x | | x], y as [y |  | y].
  2-4,6-8: right; intros; discriminate.
  2: by left.
  1,2: nrapply decidable_iff.
  1,3: split.
  1,3: nrapply ap.
  1,2: intros H; by injection H.
  1,2: exact _.
Defined.

(** By Hedberg's theorem, we have that the integers are a set. *)
Global Instance ishset_int@{} : IsHSet Int := _.

(** *** Pointedness *)

(** We sometimes want to treat the integers as a pointed type with basepoint given by 0. *)
Global Instance ispointed_int : IsPointed Int := 0.

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
  by destruct x.
Defined.

(** Negation is an equivalence. *)
Global Instance isequiv_int_neg@{} : IsEquiv int_neg.
Proof.
  snrapply (isequiv_adjointify int_neg int_neg).
  1,2: nrapply int_neg_neg.
Defined.

(** Negation is injective. *)
Definition isinj_int_neg@{} (x y : Int) : - x = - y -> x = y
  := equiv_inj int_neg.

(** The negation of a successor is the predecessor of the negation. *)
Definition int_neg_succ (x : Int) : - x.+1 = (- x).-1.
Proof.
  by destruct x as [[] | | ].
Defined.

(** The negation of a predecessor is the successor of the negation. *)
Definition int_neg_pred (x : Int) : - x.-1 = (- x).+1.
Proof.
  by destruct x as [ | | []].
Defined.

(** The successor of a predecessor is the identity. *)
Definition int_pred_succ@{} (x : Int) : x.-1.+1 = x.
Proof.
  by destruct x as [ | | []].
Defined. 

(** The predecessor of a successor is the identity. *)
Definition int_succ_pred@{} (x : Int) : x.+1.-1 = x.
Proof.
  by destruct x as [[] | | ].
Defined.

(** The successor is an equivalence on [Int] *)
Global Instance isequiv_int_succ@{} : IsEquiv int_succ
  := isequiv_adjointify int_succ int_pred int_pred_succ int_succ_pred.

(** The predecessor is an equivalence on [Int] *)
Global Instance isequiv_int_pred@{} : IsEquiv int_pred
  := isequiv_inverse int_succ.

(** *** Addition *)

(** Integer addition with zero on the left is the identity by definition. *)
Definition int_add_0_l@{} (x : Int) : 0 + x = x := 1.

(** Integer addition with zero on the right is the identity. *)
Definition int_add_0_r@{} (x : Int) : x + 0 = x.
Proof.
  induction x as [|[|x] IHx|[|x] IHx].
  - reflexivity.
  - reflexivity.
  - change (?z.+1 + 0) with (z + 0).+1.
    exact (ap _ IHx).
  - reflexivity.
  - change (?z.-1 + 0) with (z + 0).-1.
    exact (ap _ IHx).
Defined. 

(** Adding a successor on the left is the successor of the sum. *)
Definition int_add_succ_l@{} (x y : Int) : x.+1 + y = (x + y).+1.
Proof.
  induction x as [|[|x] IHx|[|x] IHx] in y |- *.
  1-3: reflexivity.
  all: symmetry; apply int_pred_succ.
Defined.

(** Adding a predecessor on the left is the predecessor of the sum. *)
Definition int_add_pred_l@{} (x y : Int) : x.-1 + y = (x + y).-1.
Proof.
  induction x as [|[|x] IHx|[|x] IHx] in y |- *.
  1,4,5: reflexivity.
  all: symmetry; apply int_succ_pred.
Defined.

(** Adding a successor on the right is the successor of the sum. *)
Definition int_add_succ_r@{} (x y : Int) : x + y.+1 = (x + y).+1.
Proof.
  induction x as [|x IHx|[] IHx] in y |- *.
  - reflexivity.
  - by rewrite 2 int_add_succ_l, IHx.
  - cbn; by rewrite int_succ_pred, int_pred_succ.
  - change ((- (n.+1%nat)).-1 + y.+1 = ((- (n.+1%nat)).-1 + y).+1).
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
  - apply int_add_0_r.
  - rewrite int_add_succ_l.
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
  - by rewrite !int_add_succ_l, IHx.
  - by rewrite !int_add_pred_l, IHx.
Defined.

(** Negation is a left inverse with respect to integer addition. *)
Definition int_add_neg_l@{} (x : Int) : - x + x = 0.
Proof.
  induction x as [|x IHx|x IHx].
  - reflexivity.
  - by rewrite int_neg_succ, int_add_pred_l, int_add_succ_r, IHx.
  - by rewrite int_neg_pred, int_add_succ_l, int_add_pred_r, IHx.
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

(** Multiplication with a successor on the left is the sum of the multplication without the sucesseor and the multiplicand which was not a successor. *)
Definition int_mul_succ_l@{} (x y : Int) : x.+1 * y = y + x * y.
Proof.
  induction x as [|[|x] IHx|[] IHx] in y |- *.
  - reflexivity.
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

(** Similarly, multiplication with a predecessor on the left is the sum of the multiplication without the predecessor and the negation of the multiplicand which was not a predecessor. *)
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
Definition int_mul_0_l@{} (x : Int) : 0 * x = 0 := 1.

(** Integer multiplication with zero on the right is zero. *)
Definition int_mul_0_r@{} (x : Int) : x * 0 = 0.
Proof.
  induction x as [|x IHx|x IHx].
  - reflexivity.
  - by rewrite int_mul_succ_l, int_add_0_l.
  - by rewrite int_mul_pred_l, int_add_0_l.
Defined.

(** Integer multiplication with one on the left is the identity. *)
Definition int_mul_1_l@{} (x : Int) : 1 * x = x.
Proof.
  apply int_add_0_r.
Defined.

(** Integer multiplication with one on the right is the identity. *)
Definition int_mul_1_r@{} (x : Int) : x * 1 = x.
Proof.
  induction x as [|x IHx|x IHx].
  - reflexivity.
  - by rewrite int_mul_succ_l, IHx.
  - by rewrite int_mul_pred_l, IHx.
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

(** Multiplying with a successor on the right is the sum of the multiplication without the successor and the product of the multiplicand which was not a successor and the multiplicand. *)
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

(** Multiplying with a predecessor on the right is the sum of the multiplication without the predecessor and the product of the multiplicand which was not a predecessor and the negation of the multiplicand which was not a predecessor. *)
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

(** ** Iteration of equivalences *)

(** *** Iteration by arbitrary integers *)

(** Iteration by arbitrary integers requires the endofunction to be an equivalence, so that we can define a negative iteration by using its inverse. *)

Definition int_iter {A} (f : A -> A) `{!IsEquiv f} (n : Int) : A -> A
  := match n with
      | negS n => fun x => nat_iter n.+1%nat f^-1 x
      | zero => idmap
      | posS n => fun x => nat_iter n.+1%nat f x
     end.

Definition int_iter_neg {A} (f : A -> A) `{IsEquiv _ _ f} (n : Int) (a : A)
  : int_iter f (- n) a = int_iter f^-1 n a.
Proof.
  by destruct n.
Defined.

Definition int_iter_succ_l {A} (f : A -> A) `{IsEquiv _ _ f} (n : Int) (a : A)
  : int_iter f (int_succ n) a = f (int_iter f n a).
Proof.
  induction n as [|n|n].
  - reflexivity.
  - by destruct n.
  - rewrite int_pred_succ. 
    destruct n.
    all: symmetry; apply eisretr.
Defined.

Definition int_iter_succ_r {A} (f : A -> A) `{IsEquiv _ _ f} (n : Int) (a : A)
  : int_iter f (int_succ n) a = int_iter f n (f a).
Proof.
  induction n as [|n|n].
  - reflexivity.
  - destruct n.
    1: reflexivity.
    cbn; f_ap.
  - destruct n.
    1: symmetry; apply eissect.
    rewrite int_pred_succ.
    apply (ap f^-1).
    rhs_V nrapply IHn.
    by destruct n.
Defined.

Definition int_iter_pred_l {A} (f : A -> A) `{IsEquiv _ _ f} (n : Int) (a : A)
  : int_iter f (int_pred n) a = f^-1 (int_iter f n a).
Proof.
  (* Convert the problem to be a problem about [f^-1] and [-n]. *)
  lhs_V exact (int_iter_neg f^-1 (n.-1) a).
  rhs_V exact (ap f^-1 (int_iter_neg f^-1 n a)).
  (* Then [int_iter_succ_l] applies, after changing [- n.-1] to [(-n).+1]. *)
  rewrite int_neg_pred.
  apply int_iter_succ_l.
Defined.

Definition int_iter_pred_r {A} (f : A -> A) `{IsEquiv _ _ f} (n : Int) (a : A)
  : int_iter f (int_pred n) a = int_iter f n (f^-1 a).
Proof.
  (* Convert the problem to be a problem about [f^-1] and [-n]. *)
  lhs_V exact (int_iter_neg f^-1 (n.-1) a).
  rhs_V exact (int_iter_neg f^-1 n (f^-1 a)).
  (* Then [int_iter_succ_r] applies, after changing [- n.-1] to [(-n).+1]. *)
  rewrite int_neg_pred.
  apply int_iter_succ_r.
Defined.

Definition int_iter_add {A} (f : A -> A) `{IsEquiv _ _ f} (m n : Int)
  : int_iter f (m + n) == int_iter f m o int_iter f n.
Proof.
  intros a.
  induction m as [|m|m].
  - reflexivity.
  - rewrite int_add_succ_l.
    rewrite 2 int_iter_succ_l.
    f_ap.
  - rewrite int_add_pred_l.
    rewrite 2 int_iter_pred_l.
    f_ap.
Defined.

(** If [g : A -> A'] commutes with automorphisms of [A] and [A'], then it commutes with iteration. *)
Definition int_iter_commute_map {A A'} (f : A -> A) `{!IsEquiv f}
  (f' : A' -> A') `{!IsEquiv f'}
  (g : A -> A') (p : g o f == f' o g) (n : Int) (a : A)
  : g (int_iter f n a) = int_iter f' n (g a).
Proof.
  induction n as [|n IHn|n IHn] in a |- *.
  - reflexivity.
  - rewrite 2 int_iter_succ_r.
    rewrite IHn.
    f_ap.
  - rewrite 2 int_iter_pred_r.
    rewrite IHn.
    f_ap.
    apply moveL_equiv_V.
    lhs_V nrapply p.
    f_ap.
    apply eisretr.
Defined.

(** In particular, homotopic maps have homotopic iterations. *)
Definition int_iter_homotopic (n : Int) {A} (f f' : A -> A) `{!IsEquiv f} `{!IsEquiv f'}
  (h : f == f')
  : int_iter f n == int_iter f' n
  := int_iter_commute_map f f' idmap h n.

(** [int_iter f n x] doesn't depend on the proof that [f] is an equivalence. *)
Definition int_iter_agree (n : Int) {A} (f : A -> A) {ief ief' : IsEquiv f}
  : forall x, @int_iter A f ief n x = @int_iter A f ief' n x
  := int_iter_homotopic n f f (fun _ => idpath).

Definition int_iter_invariant (n : Int) {A} (f : A -> A) `{!IsEquiv f}
  (P : A -> Type)
  (Psucc : forall x, P x -> P (f x))
  (Ppred : forall x, P x -> P (f^-1 x))
  : forall x, P x -> P (int_iter f n x).
Proof.
  induction n as [|n IHn|n IHn]; intro x.
  - exact idmap.
  - intro H.
    rewrite int_iter_succ_l.
    apply Psucc, IHn, H.
  - intro H.
    rewrite int_iter_pred_l.
    apply Ppred, IHn, H.
Defined.

(** ** Exponentiation of loops *)

Definition loopexp {A : Type} {x : A} (p : x = x) (z : Int) : (x = x)
  := int_iter (equiv_concat_r p x) z idpath.

Definition loopexp_succ_r {A : Type} {x : A} (p : x = x) (z : Int)
  : loopexp p z.+1 = loopexp p z @ p
  := int_iter_succ_l _ _ _.

Definition loopexp_pred_r {A : Type} {x : A} (p : x = x) (z : Int)
  : loopexp p z.-1 = loopexp p z @ p^
  := int_iter_pred_l _ _ _.

Definition loopexp_succ_l {A : Type} {x : A} (p : x = x) (z : Int)
  : loopexp p z.+1 = p @ loopexp p z.
Proof.
  lhs nrapply loopexp_succ_r.
  induction z as [|z|z].
  - nrapply concat_1p_p1.
  - rewrite loopexp_succ_r.
    rhs nrapply concat_p_pp.
    f_ap.
  - rewrite loopexp_pred_r.
    lhs nrapply concat_pV_p.
    rhs nrapply concat_p_pp.
    by apply moveL_pV.
Defined.

Definition loopexp_pred_l {A : Type} {x : A} (p : x = x) (z : Int)
  : loopexp p z.-1 = p^ @ loopexp p z.
Proof.
  rewrite loopexp_pred_r.
  induction z as [|z|z].
  - exact (concat_1p _ @ (concat_p1 _)^).
  - rewrite loopexp_succ_r.
    lhs nrapply concat_pp_V.
    rhs nrapply concat_p_pp.
    by apply moveL_pM.
  - rewrite loopexp_pred_r.
    rhs nrapply concat_p_pp.
    f_ap.
Defined.

Definition ap_loopexp {A B} (f : A -> B) {x : A} (p : x = x) (z : Int)
  : ap f (loopexp p z) = loopexp (ap f p) z.
Proof.
  nrapply int_iter_commute_map.
  intro q; apply ap_pp.
Defined.

Definition loopexp_add {A : Type} {x : A} (p : x = x) m n
  : loopexp p (m + n) = loopexp p m @ loopexp p n.
Proof.
  induction m as [|m|m].
  - symmetry; apply concat_1p.
  - rewrite int_add_succ_l.
    rewrite 2 loopexp_succ_l.
    by rewrite IHm, concat_p_pp.
  - rewrite int_add_pred_l.
    rewrite 2 loopexp_pred_l.
    by rewrite IHm, concat_p_pp.
Defined.

(** Under univalence, exponentiation of loops corresponds to iteration of autoequivalences. *)

Definition equiv_path_loopexp {A : Type} (p : A = A) (z : Int) (a : A)
  : equiv_path A A (loopexp p z) a = int_iter (equiv_path A A p) z a.
Proof.
  refine (int_iter_commute_map _ _ (fun p => equiv_path A A p a) _ _ _).
  intro q; cbn.
  nrapply transport_pp.
Defined.

Definition loopexp_path_universe `{Univalence} {A : Type} (f : A <~> A)
  (z : Int) (a : A)
  : transport idmap (loopexp (path_universe f) z) a = int_iter f z a.
Proof.
  revert f. equiv_intro (equiv_path A A) p.
  refine (_ @ equiv_path_loopexp p z a).
  refine (ap (fun q => equiv_path A A (loopexp q z) a) _).
  apply eissect.
Defined.

(** ** Converting between integers and naturals *)

(** [int_of_nat] preserves successors. *)
Definition int_nat_succ (n : nat)
  : (n.+1)%int = (n.+1)%nat :> Int.
Proof.
  by induction n.
Defined.

(** [int_of_nat] preserves addition. Hence is a monoid homomorphism. *)
Definition int_nat_add (n m : nat)
  : (n + m)%int = (n + m)%nat :> Int.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - rewrite <- 2 int_nat_succ.
    rewrite int_add_succ_l.
    exact (ap _ IHn).
Defined.

(** [int_of_nat] preserves subtraction when not truncated. *)
Definition int_nat_sub (n m : nat)
  : (m <= n)%nat -> (n - m)%int = (n - m)%nat :> Int.
Proof.
  intros H.
  induction H as [|n H IHn].
  - lhs nrapply int_add_neg_r.
    by rewrite nat_sub_cancel.
  - rewrite nat_sub_succ_l; only 2: exact _.
    rewrite <- 2 int_nat_succ.
    rewrite int_add_succ_l.
    exact (ap _ IHn).
Defined.

(** [int_of_nat] preserves multiplication. This makes [int_of_nat] a semiring homomorphism. *)
Definition int_nat_mul (n m : nat)
  :  (n * m)%int = (n * m)%nat :> Int.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - rewrite <- int_nat_succ.
    rewrite int_mul_succ_l.
    rewrite nat_mul_succ_l.
    rhs_V nrapply int_nat_add.
    exact (ap _ IHn).
Defined.
