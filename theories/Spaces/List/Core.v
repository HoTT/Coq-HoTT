Require Import Basics.Overture.

Local Unset Elimination Schemes.
Local Set Universe Minimization ToSet.
Local Set Polymorphic Inductive Cumulativity.

(** * Lists *)

(** ** Definition *)

Declare Scope list_scope.
Local Open Scope list_scope.

(** A list is a sequence of elements from a type [A]. This is a very useful datatype and has many applications ranging from programming to algebra. It can be thought of a free monoid. *)
Inductive list@{i|} (A : Type@{i}) : Type@{i} :=
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

(** A tactic for doing induction over a list that avoids spurious universes. *)
Ltac simple_list_induction l h t IH :=
  try generalize dependent l;
  fix IH 1;
  intros [| h t];
  [ clear IH | specialize (IH t) ].

(** Syntactic sugar for creating lists. [ [a1, b2, ..., an] = a1 :: b2 :: ... :: an :: nil ]. *)
Notation "[ x ]" := (x :: nil) : list_scope.
Notation "[ x , y , .. , z ]" := (x :: (y :: .. (z :: nil) ..)) : list_scope.

(** ** Length *)

(** Notice that the definition of a list looks very similar to the definition of [nat]. It is as if each [S] constructor from [nat] has an element of [A] attached to it. We can discard this extra element and get a list invariant that we call [length]. *)

(** The length (number of elements) of a list. *)
Fixpoint length {A : Type} (l : list A) :=
  match l with
  | nil => O
  | _ :: l => S (length l)
  end.

(** ** Concatenation *)

(** Given two lists [ [a1; a2; ...; an] ] and [ [b1; b2; ...; bm] ], we can concatenate them to get [ [a1; a2; ...; an; b1; b2; ...; bm] ]. *)
Definition app {A : Type} : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app : list_scope.

(** ** Folding *)

(** Folding is a very important operation on lists. It is a way to reduce a list to a single value. The [fold_left] function starts from the left and the [fold_right] function starts from the right. *)

(** [fold_left f l a0] computes [f (... (f (f a0 x1) x2) ...) xn] where [l = [x1; x2; ...; xn]]. *)
Fixpoint fold_left {A B} (f : A -> B -> A) (l : list B) (default : A) : A :=
  match l with
    | nil => default
    | cons b l => fold_left f l (f default b)
  end.

(** [fold_right f a0 l] computes [f x1 (f x2 ... (f xn a0) ...)] where [l = [x1; x2; ...; xn]]. *)
Fixpoint fold_right {A B} (f : B -> A -> A) (default : A) (l : list B) : A :=
  match l with
    | nil => default
    | cons b l => f b (fold_right f default l)
  end.

(** ** Maps - Functoriality of Lists *)

(** The [list_map] function applies a function to each element of a list. In other words [ list_map f [a1; a2; ...; an] = [f a1; f a2; ...; f an] ]. *)
Fixpoint list_map {A B : Type} (f : A -> B) (l : list A) :=
  match l with
  | nil => nil
  | x :: l => (f x) :: (list_map f l)
  end.

(** The [list_map2] function applies a binary function to corresponding elements of two lists. When one of the lists run out, it uses one of the default functions to fill in the rest. *)
Fixpoint list_map2 {A B C : Type} (f : A -> B -> C)
  (def_l : list A -> list C) (def_r : list B -> list C) l1 l2 :=
  match l1, l2 with
  | nil, nil => nil
  | nil, _ => def_r l2
  | _, nil => def_l l1
  | x :: l1, y :: l2 => (f x y) :: (list_map2 f def_l def_r l1 l2)
  end.

(** ** Reversal *)

(** Tail-recursive list reversal. *)
Fixpoint reverse_acc {A : Type} (acc : list A) (l : list A) : list A :=
  match l with
  | nil => acc
  | x :: l => reverse_acc (x :: acc) l
  end.

(** Reversing the order of a list. The list [ [a1; a2; ...; an] ] becomes [ [an; ...; a2; a1] ]. *)
Definition reverse {A : Type} (l : list A) : list A := reverse_acc nil l.

(** ** Getting Elements *)

(** The head of a list is its first element. Returns [None] If the list is empty. *)
Definition head {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | a :: _ => Some a
  end.

(** The tail of a list is the list without its first element. *)
Definition tail {A : Type} (l : list A) : list A :=
  match l with
    | nil => nil
    | a :: m => m
  end.

(** The last element of a list. If the list is empty, it returns [None]. *)
Fixpoint last {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | a :: nil => Some a
  | _ :: l => last l
  end.

(** The [n]-th element of a list. If the list is too short, it returns [None]. *)
Fixpoint nth {A : Type} (l : list A) (n : nat) : option A :=
  match n, l with
  | O, x :: _ => Some x
  | S n, _ :: l => nth l n
  | _, _ => None
  end.

(** ** Removing Elements *)

(** Remove the last element of a list and do nothing if it is empty. *)
Fixpoint remove_last {A : Type} (l : list A) : list A :=
  match l with
  | nil => nil
  | _ :: nil => nil
  | x :: l => x :: remove_last l
  end.

(** ** Sequences *)

(** Descending sequence of natural numbers starting from [n.-1] to [0]. *)
Fixpoint seq_rev (n : nat) : list nat :=
    match n with
    | O => nil
    | S n => n :: seq_rev n
    end.

(** Ascending sequence of natural numbers [< n]. *)
Definition seq (n : nat) : list nat := reverse (seq_rev n).

(** ** Repeat *)

(** Repeat an element [n] times. *)
Fixpoint repeat {A : Type} (x : A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n => x :: repeat x n
  end.

(** ** Membership Predicate *)

(** The "In list" predicate *)
Fixpoint InList@{i|} {A : Type@{i}} (a : A) (l : list A) : Type@{i} :=
  match l with
    | nil => Empty
    | b :: m => (b = a) + InList a m
  end.

(** ** Forall *)

(** Apply a predicate to all elements of a list and take their conjunction. *)
Fixpoint for_all@{i j|} {A : Type@{i}} (P : A -> Type@{j}) l : Type@{j} :=
  match l with
  | nil => Unit
  | x :: l => P x /\ for_all P l
  end.

(** ** Exists *)

(** Apply a predicate to all elements of a list and take their disjunction. *)
Fixpoint list_exists@{i j|} {A : Type@{i}} (P : A -> Type@{j}) l : Type@{j} :=
  match l with
  | nil => Empty
  | x :: l => P x + list_exists P l
  end.
