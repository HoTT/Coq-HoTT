Require Import Basics.
Require Import Types.
Require Import Classes.interfaces.abstract_algebra.

(* This file contains results on groups *)

Lemma left_mult_equiv `{Group G} : G -> G <~> G.
Proof.
  intro x.
  serapply equiv_adjointify.
  + intro y; exact (x & y).
  + intro y; exact (Anegate x & y).
  + intro y.
    rewrite associativity.
    rewrite right_inverse.
    apply left_identity.
  + intro y.
    rewrite associativity.
    rewrite (left_inverse x).
    apply left_identity.
Defined.

Lemma right_mult_equiv `{Group G} : G -> G <~> G.
Proof.
  intro x.
  serapply equiv_adjointify.
  + intro y; exact (y & x).
  + intro y; exact (y & Anegate x).
  + intro y.
    rewrite <- (associativity y _ x).
    rewrite (left_inverse x).
    apply right_identity.
  + intro y.
    rewrite <- (associativity y x).
    rewrite right_inverse.
    apply right_identity.
Defined.
