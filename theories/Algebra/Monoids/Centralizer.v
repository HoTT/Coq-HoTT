Require Import Basics.Overture Basics.Tactics.
Require Import Algebra.Monoids.Monoid.

Local Open Scope mc_mult_scope.

(** * Centralizers *)

(** The centralizer of [g] consists of the elements that commute with [g]. We only need a binary operation so this concept is not special to monoids. *)
Definition centralizer {A : Type} `{SgOp A} (g h : A)
  := g * h = h * g.

(** A two-sided identity commutes with every element. *)
Definition centralizer_unit {A : Type} `{SgOp A} {Aunit : MonUnit A}
  `{!LeftIdentity _ mon_unit, !RightIdentity _ mon_unit} (g : A) 
  : centralizer g mon_unit
  := right_identity g @ (left_identity g)^.

(** Associativity alone makes each centralizer closed under the operation. *)
Definition centralizer_sgop {A : Type} `{SgOp A, !Associative (.*.)} 
  (g h k : A) (p : centralizer g h) (q : centralizer g k)
  : centralizer g (h * k).
Proof.
  unfold centralizer.
  lhs tapply associativity.
  lhs napply (ap (.* k) p).
  lhs_V tapply associativity.
  lhs napply (ap (h *.) q).
  tapply associativity.
Defined.
