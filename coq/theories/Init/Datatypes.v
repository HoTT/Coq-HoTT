(* Bits an pieces from Coq's Init/Datatypes.v *)
Set Implicit Arguments.

Require Import Logic.
Declare ML Module "nat_syntax_plugin".

(** [option A] is the extension of [A] with an extra element [None] *)

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Arguments None [A].

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B: Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Notation "A \/ B" := (A + B)%type : type_scope.
Notation or := sum.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "A /\ B" := (A * B)%type : type_scope. 
Notation and := prod.
Notation conj := pair.

Definition fst {A B : Type} (p : A * B) := match p with (x, y) => x end.
Definition snd {A B : Type} (p : A * B) := match p with (x, y) => y end.

Hint Resolve pair inl inr : core.

Definition prod_curry (A B C:Type) (f:A -> B -> C)
  (p:prod A B) : C := match p with
                       | pair x y => f x y
                       end.

(** <-> is wanted by ssreflect so we hack it here. *)
(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

(* Definition iff (A B : Type) := prod (A -> B) (B -> A). *)

(* Notation "A <-> B" := (iff A B) : type_scope. *)
(* assia : I change the definition of iff for an inductive one *)

Inductive iff (A B : Type) : Type :=
  Iff: (A -> B) -> (B -> A) -> iff A B.
Notation "A <-> B" := (iff A B) : type_scope.


(** [Empty_set] is a datatype with no inhabitant *)

Inductive Empty_set : Type :=.

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Type :=
    tt : unit.

(** [bool] is the datatype of the boolean values [true] and [false] *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

Add Printing If bool.

Delimit Scope bool_scope with bool.

Bind Scope bool_scope with bool.

Definition andb (b1 b2:bool) : bool := if b1 then b2 else false.

Definition orb (b1 b2:bool) : bool := if b1 then true else b2.

Definition negb (b:bool) := if b then false else true.

Definition implb (b1 b2:bool) : bool := if b1 then b2 else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.

(* Natural numbers. *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Arguments S _.

Open Scope nat_scope. (* Originally in Peano.v *)


(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [refl_identity A a] *)

Inductive identity (A:Type) (a:A) : A -> Type :=
  identity_refl : identity a a.

Hint Resolve identity_refl: core.

Arguments identity {A} a _.
Arguments identity_refl {A a} , [A] a.

Arguments identity_ind [A] a P f y i.
Arguments identity_rec [A] a P f y i.
Arguments identity_rect [A] a P f y i.


(** Identity type *)

Definition ID := forall A:Type, A -> A.
Definition id : ID := fun A x => x.


Notation "x = y :> A" := (@identity A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

(** Another way of interpreting booleans as propositions *)

Definition is_true b := b = true.

(** Polymorphic lists and some operations *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Arguments nil [A].
Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Local Open Scope list_scope.
(** Concatenation of two lists *)

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list_scope.
