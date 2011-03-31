(** In this example we show how to use the [firstorder] tactic to
   prove statements in first-order logic. We consider the Frobenius
   rule, which states that existential quantifiers and conjunctions
   commute.
*)

Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) : 
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
(** We stated a theorem with _parameters_ [A], [p] and [q]. An
   alternative would be to quantify universally over [A], [p] and [q].
   Both forms are acceptable. Coq 8.3 will automatically perform the [intros]
   rule on parameters. *)
Proof.
  (** Coq's [firstorder] tactic is used for intuitionistic first-order reasoning.
     Let us try it. *)
  firstorder.
  (** And we are done. *)
Qed.

(** According to the Curry-Howard isomorphism there is a
   correspondence between propositions and sets/types. Thus there is
   also a set-theoretic version of Frobenius rule. *)
Theorem frobenius_set1 (A : Set) (p : A -> Set) (q : Set) :
  ({x : A & q * p x} -> q * {x : A & p x})%type.
(** The above notation requires some explanation. First of all, the enclosing
   [(...)%type] is there to tell Coq that the [*] symbol should be interpreted
   in the context of types, as opposed to natural numbers. Without it, Coq thinks
   that [q * p x] is multiplication of natural numbers and complains accordingly.
   The notation [{x : A & ...}] means "the set of all [x]'s from [A] that satisfy
   the condition ...". Also, equivalence [<->] is only used for propositions, so
   have to split the theorem into two function spaces (implications) by hand. *)
Proof.
  firstorder.
Qed.

Theorem frobenius_set2 (A : Set) (p : A -> Set) (q : Set) :
  (q * {x : A & p x} -> {x : A & q * p x})%type.
Proof.
  firstorder.
Qed.

(** What proofs did [firstoder] actually find? *)
Print frobenius_set2.
(** Uhhhh. *)

(* Here are some exercise. *)

(* Exercise: in [frobenius], replace conjunctions with disjunctions
   and see what [firstorder] reduces the statement to. You will discover
   a missing condition. Add the condition to the original statement and
   rerun [firstorder]. *)

(* Exercise: the dual Frobenius rule says that universal quantifiers
   commute with disjunctions. State the theorem and prove it using
   the Law of Excluded Middle. *)

(* Exercise (hard): prove that the dual Frobenius rule is actually equivalent
   to the Law of Excluded Middle. *)
