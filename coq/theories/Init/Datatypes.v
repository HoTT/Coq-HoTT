(* Bits an pieces from Coq's Init/Datatypes.v *)

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)


Require Export Logic.

(*Add Rec ML Path "/Users/andrej/Documents/project/homotopy/coq/plugins".*)
(*Declare ML Module "nat_syntax_plugin".*)

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Arguments pair {A B} _ _.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Definition fst {A B : Type} (p : A * B) := match p with (x, y) => x end.
Definition snd {A B : Type} (p : A * B) := match p with (x, y) => y end.

Hint Resolve pair : core.

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

(* Natural numbers. *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Arguments S _.

Open Scope nat_scope. (* Originally in Peano.v *)
