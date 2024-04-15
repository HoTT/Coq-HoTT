Require Import Basics.Overture.

Unset Elimination Schemes.

(** * Lists *)

(** ** Definition *)

Declare Scope list_scope.
Local Open Scope list_scope.

(** TODO: description of list needs improvement. *)

(** A list is a sequence of elements from a type [A]. This is a very useful datatype and has many applications ranging from programming to algebra. It can be thought of a free monoid. *)
Inductive list@{i} (A : Type@{i}) : Type@{i} :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

Delimit Scope list_scope with list.
Bind Scope list_scope with list.

(** This messes with Coq's parsing of [] in ltac. Therefore we keep it commented out. It's not difficult to write [nil] instead. *)
(* Notation "[]" := nil : list_scope. *)
Infix "::" := cons : list_scope.

Scheme list_rect := Induction for list Sort Type.
Scheme list_ind := Induction for list Sort Type.
Scheme list_rec := Minimality for list Sort Type.

(** Syntactic sugar for creating lists. *)
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; y ; .. ; z ] " :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.

(** ** Length *)

(** Notice that the definition of a list looks very similar to the definition of [nat]. It is as if each [S] constructor from [nat] has an element of [A] attached to it. We can discard this extra element and get a list invariant that we call [length]. *)

(** The length (number of elements) of a list. *)
Fixpoint length {A} (l : list A) :=
  match l with
  | nil => O
  | _ :: l => S (length l)
  end.

(** ** Concatenation *)

Definition app {A : Type} : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app : list_scope.

(** ** Folding *)

Fixpoint fold_left {A B} (f : A -> B -> A) (l : list B) (a0 : A) : A :=
  match l with
    | nil => a0
    | cons b l => fold_left f l (f a0 b)
  end.

Fixpoint fold_right {A B} (f : B -> A -> A) (default : A) (l : list B) : A :=
  match l with
    | nil => default
    | cons b l => f b (fold_right f default l)
  end.

(** ** Maps *)

Fixpoint map {A B} (f : A -> B) (l : list A) :=
  match l with
  | nil => nil
  | x :: l => (f x) :: (map f l)
  end.

Fixpoint map2 {A B C} (f : A -> B -> C)
  (def_l : list A -> list C) (def_r : list B -> list C)
  l1 l2 :=
  match l1, l2 with
  | nil, nil => nil
  | nil, _ => def_r l2
  | _, nil => def_l l1
  | x :: l1, y :: l2 => (f x y) :: (map2 f def_l def_r l1 l2)
  end.

(** ** Reversal *)

(** Tail-recursive list reversal. *)
Fixpoint reverse_acc {A} (acc : list A) (l : list A) : list A :=
  match l with
  | nil => acc
  | x :: l => reverse_acc (x :: acc) l
  end.

(** Reversing the order of a list. *)
Definition reverse {A} (l : list A) : list A := reverse_acc nil l.

(** ** Getting Elements *)

(* Copy pasted from the Coq library. *)
Definition tl {A} (l:list A) : list A :=
  match l with
    | nil => nil
    | a :: m => m
  end.

(** The last element of a list. *)
Fixpoint last {A} (default : A) (l : list A) : A :=
  match l with
  | nil => default
  | _ :: l => last default l
  end.

(** The [n]-th element of a list. *)
Fixpoint nth {A} (l : list A) (n : nat) (default : A) : A :=
  match n, l with
  | O, x :: _ => x
  | S n, _ :: l => nth l n default
  | _, _ => default
  end.

(** ** Removing Elements *)

(** Remove the last element of a list and do nothing if empty. *)
Fixpoint remove_last {A} (l : list A) : list A :=
  match l with
  | nil => nil
  | _ :: nil => nil
  | x :: l => x :: remove_last l
  end.

(** ** Sequences *)

(** Descending sequence of natural numbers starting from [n.-1]. *)
Fixpoint seq_rev (n : nat) : list nat :=
    match n with
    | O => nil
    | S n => n :: seq_rev n
    end.

(** Ascending sequence of natural numbers [< n]. *)
Definition seq (n : nat) : list nat := reverse (seq_rev n).

(** ** Membership Predicate *)

(** The "In list" predicate *)
Fixpoint InList {A} (a : A) (l : list A) : Type0 :=
  match l with
    | nil => Empty 
    | b :: m => (b = a) + InList a m
  end.

(** ** Forall *)

Fixpoint for_all {A} (P : A -> Type) l : Type :=
  match l with
  | nil => Unit
  | x :: l => P x /\ for_all P l
  end.
