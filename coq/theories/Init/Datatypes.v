(* Bits an pieces from Coq's Init/Datatypes.v *)

Require Import Logic.
Declare ML Module "nat_syntax_plugin".

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B: Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Definition fst {A B : Type} (p : A * B) := match p with (x, y) => x end.
Definition snd {A B : Type} (p : A * B) := match p with (x, y) => y end.

Hint Resolve pair inl inr : core.

(** <-> is wanted by ssreflect so we hack it here. *)
(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B : Type) := prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

(** [(sigT A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type. *)

Inductive sigT {A:Type} (P:A -> Type) : Type :=
    existT : forall x : A, P x -> sigT P.

Arguments sigT (A P)%type.
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Add Printing Let sigT.

Definition projT1 {A : Type} {P : A -> Type} (x : sigT P) : A :=
  match x with | existT a _ => a end.

Definition projT2 {A : Type} {P : A -> Type} (x : sigT P) : P (projT1 x) :=
  match x return P (projT1 x) with | existT _ h => h end.

(** [Empty_set] is a datatype with no inhabitant *)

Inductive Empty_set : Set :=.

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set :=
    tt : unit.

(** [bool] is the datatype of the boolean values [true] and [false] *)

Inductive bool : Set :=
  | true : bool
  | false : bool.

Add Printing If bool.

Delimit Scope bool_scope with bool.

Bind Scope bool_scope with bool.

(* Natural numbers. *)

Inductive nat : Set :=
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
  identity_refl : identity A a a.

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

