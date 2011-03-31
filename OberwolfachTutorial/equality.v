(** Coq comes equipped with a notion of equality which is called "convertibility"
   or "definitional equality" in Martin-Löf type theory.
   
   But we can also define another kind of equality, known as "propositional equality",
   with inductive types. *)
   
(** The following definition says that for every set [A] there is a binary
   relation [equ] which has one introduction rule [refl] expressing the fact
   that [equ] is a reflexive relation.

   The fact that we put [A] in curly braces means that it is an _implicit_
   argument, in other words we write [equ x y] instead of [equ A x y]. This
   is possible because Coq computes [A] as the type of [x].
*)

Inductive equ {A : Set} : A -> A -> Prop :=
  | refl : forall x : A, equ x x.

(* Coq also generated an induction principle [equ_ind] for [equ].
   It says that [equ] is the least reflexive relation on [A]. *)
Print equ_ind.

(* Coq allows us to define new notation with the [Notation] keyword.
   Here we tell it that [x == y] means [equ x y]. This is not to be
   confused with [x = y] which is a short-hand for the predefined
   equality [eq x y]. *)
Notation "x == y" := (equ x y) (at level 70, no associativity).

(* Let us prove that [equ] has the desired properties. *)

(* Reflexivity. *)
Theorem equ_refl (A : Set) : forall x : A, x == x.
Proof.
  apply refl.
Qed.

Theorem equ_symm (A : Set) : forall x y : A, x == y -> y == x.
Proof.
  intros x y E.
  induction E.
  apply refl.
Qed.

Theorem equ_tran (A : Set) : forall x y z : A, x == y -> y == z -> x == z.
Proof.
  intros x y z E1 E2.
  induction E1.
  assumption.
Qed.
  
(* Substitution of equals for equals. *)
Theorem equ_subst (A : Set) (p : A -> Prop) (x y : A) :
  p x -> x == y -> p y.
Proof.
  intros H E.
  induction E.
  assumption.
Qed.

(* Leibniz's law. *)
Theorem leibniz (A : Set) (x y : A) :
  (forall p : A -> Prop, (p x -> p y)) <-> x == y.
Proof.
  split.
  intro L.
  apply L with (p := (fun z : A => x == z)).
  apply refl.
  intro E.
  induction E.
  auto.
Qed.

(* Here is an alternative definition of equality. It says that
   for every [x : A] we have an inductively defined predicate
   [equ' x : A -> Prop] which has one introduction rule. *)

Inductive equ' {A : Set} (x : A) : A -> Prop :=
  | refl' : equ' x x.

(* What does the induction principle look like now? *)
Print equ'_ind.
(* It is subsitution of equals for equals. *)

(* Exercise: show that [equ' x y] and [equ x y] are equivalent. *)

(* Exercise: how is Coq equality [eq] defined, as [equ] or [equ']? *)

