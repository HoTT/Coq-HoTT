(* Bits an pieces from Coq's Init/Datatypes.v *)

Require Export Logic.
Declare ML Module "nat_syntax_plugin".

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B: Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

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

Definition prod (A B : Type) := sigT (fun _ : A => B).

Notation "x * y" := (prod x y) : type_scope.

Definition pair {A B : Type} (a : A) (b : B) : A * B := 
       existT (fun _ : A => B) a b.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Definition fst {A B : Type} (p : A * B) := 
   let (x, _ ) := p in x.

Definition snd {A B : Type} (p : A * B) := 
  match p with existT a b => b end.

Hint Resolve pair inl inr : core.

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
