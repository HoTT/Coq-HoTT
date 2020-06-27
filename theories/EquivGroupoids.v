(* -*- mode: coq; mode: visual-line -*-  *)

(** * The pregroupid structure of [Equiv] *)

Require Import Basics.Overture Basics.Equivalences Types.Equiv.

Local Open Scope equiv_scope.

(** See PathGroupoids.v for the naming conventions *)
(** TODO: Consider using a definition of [IsEquiv] and [Equiv] for which more of these are judgmental, or at least don't require [Funext]. *)
Section AssumeFunext.
  Context `{Funext}.
  (** ** The 1-dimensional groupoid structure. *)

  (** The identity equivalence is a right unit. *)
  Lemma ecompose_e1 {A B} (e : A <~> B) : e oE 1 = e.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  (** The identity is a left unit. *)
  Lemma ecompose_1e {A B} (e : A <~> B) : 1 oE e = e.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  (** Composition is associative. *)
  Definition ecompose_e_ee {A B C D} (e : A <~> B) (f : B <~> C) (g : C <~> D)
  : g oE (f oE e) = (g oE f) oE e.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  Definition ecompose_ee_e {A B C D} (e : A <~> B) (f : B <~> C) (g : C <~> D)
  : (g oE f) oE e = g oE (f oE e).
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  (** The left inverse law. *)
  Lemma ecompose_eV {A B} (e : A <~> B) : e oE e^-1 = 1.
  Proof.
    apply path_equiv; apply path_forall; intro; apply eisretr.
  Defined.

  (** The right inverse law. *)
  Lemma ecompose_Ve {A B} (e : A <~> B) : e^-1 oE e = 1.
  Proof.
    apply path_equiv; apply path_forall; intro; apply eissect.
  Defined.

  (** Several auxiliary theorems about canceling inverses across associativity.  These are somewhat redundant, following from earlier theorems.  *)

  Definition ecompose_V_ee {A B C} (e : A <~> B) (f : B <~> C)
  : f^-1 oE (f oE e) = e.
  Proof.
    apply path_equiv; apply path_forall; intro; simpl; apply eissect.
  Defined.

  Definition ecompose_e_Ve {A B C} (e : A <~> B) (f : C <~> B)
  : e oE (e^-1 oE f) = f.
  Proof.
    apply path_equiv; apply path_forall; intro; simpl; apply eisretr.
  Defined.

  Definition ecompose_ee_V {A B C} (e : A <~> B) (f : B <~> C)
  : (f oE e) oE e^-1 = f.
  Proof.
    apply path_equiv; apply path_forall; intro; simpl; apply ap; apply eisretr.
  Defined.

  Definition ecompose_eV_e {A B C} (e : B <~> A) (f : B <~> C)
  : (f oE e^-1) oE e = f.
  Proof.
    apply path_equiv; apply path_forall; intro; simpl; apply ap; apply eissect.
  Defined.

  (** Inverse distributes over composition *)
  Definition einv_ee {A B C} (e : A <~> B) (f : B <~> C)
  : (f oE e)^-1 = e^-1 oE f^-1.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  Definition einv_Ve {A B C} (e : A <~> C) (f : B <~> C)
  : (f^-1 oE e)^-1 = e^-1 oE f.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  Definition einv_eV {A B C} (e : C <~> A) (f : C <~> B)
  : (f oE e^-1)^-1 = e oE f^-1.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  Definition einv_VV {A B C} (e : A <~> B) (f : B <~> C)
  : (e^-1 oE f^-1)^-1 = f oE e.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  (** Inverse is an involution. *)
  Definition einv_V {A B} (e : A <~> B)
  : (e^-1)^-1 = e.
  Proof.
    apply path_equiv; reflexivity.
  Defined.

  (** *** Theorems for moving things around in equations. *)
  Definition emoveR_Me {A B C} (e : B <~> A) (f : B <~> C) (g : A <~> C)
  : e = g^-1 oE f -> g oE e = f.
  Proof.
    intro h.
    refine (ap (fun e => g oE e) h @ ecompose_e_Ve _ _).
  Defined.

  Definition emoveR_eM {A B C} (e : B <~> A) (f : B <~> C) (g : A <~> C)
  : g = f oE e^-1 -> g oE e = f.
  Proof.
    intro h.
    refine (ap (fun g => g oE e) h @ ecompose_eV_e _ _).
  Defined.

  Definition emoveR_Ve {A B C} (e : B <~> A) (f : B <~> C) (g : C <~> A)
  : e = g oE f -> g^-1 oE e = f.
  Proof.
    intro h.
    refine (ap (fun e => g^-1 oE e) h @ ecompose_V_ee _ _).
  Defined.

  Definition emoveR_eV {A B C} (e : A <~> B) (f : B <~> C) (g : A <~> C)
  : g = f oE e -> g oE e^-1 = f.
  Proof.
    intro h.
    refine (ap (fun g => g oE e^-1) h @ ecompose_ee_V _ _).
  Defined.

  Definition emoveL_Me {A B C} (e : A <~> B) (f : A <~> C) (g : B <~> C)
  : g^-1 oE f = e -> f = g oE e.
  Proof.
    intro h.
    refine ((ecompose_e_Ve _ _)^ @ ap (fun e => g oE e) h).
  Defined.

  Definition emoveL_eM {A B C} (e : A <~> B) (f : A <~> C) (g : B <~> C)
  : f oE e^-1 = g -> f = g oE e.
  Proof.
    intro h.
    refine ((ecompose_eV_e _ _)^ @ ap (fun g => g oE e) h).
  Defined.

  Definition emoveL_Ve {A B C} (e : A <~> C) (f : A <~> B) (g : B <~> C)
  : g oE f = e -> f = g^-1 oE e.
  Proof.
    intro h.
    refine ((ecompose_V_ee _ _)^ @ ap (fun e => g^-1 oE e) h).
  Defined.

  Definition emoveL_eV {A B C} (e : A <~> B) (f : B <~> C) (g : A <~> C)
  : f oE e = g -> f = g oE e^-1.
  Proof.
    intro h.
    refine ((ecompose_ee_V _ _)^ @ ap (fun g => g oE e^-1) h).
  Defined.

  Definition emoveL_1M {A B} (e f : A <~> B)
  : e oE f^-1 = 1 -> e = f.
  Proof.
    intro h.
    refine ((ecompose_eV_e _ _)^ @ ap (fun ef => ef oE f) h @ ecompose_1e _).
  Defined.

  Definition emoveL_M1 {A B} (e f : A <~> B)
  : f^-1 oE e = 1 -> e = f.
  Proof.
    intro h.
    refine ((ecompose_e_Ve _ _)^ @ ap (fun fe => f oE fe) h @ ecompose_e1 _).
  Defined.

  Definition emoveL_1V {A B} (e : A <~> B) (f : B <~> A)
  : e oE f = 1 -> e = f^-1.
  Proof.
    intro h.
    refine ((ecompose_ee_V _ _)^ @ ap (fun ef => ef oE f^-1) h @ ecompose_1e _).
  Defined.

  Definition emoveL_V1 {A B} (e : A <~> B) (f : B <~> A)
  : f oE e = 1 -> e = f^-1.
  Proof.
    intro h.
    refine ((ecompose_V_ee _ _)^ @ ap (fun fe => f^-1 oE fe) h @ ecompose_e1 _).
  Defined.

  Definition emoveR_M1 {A B} (e f : A <~> B)
  : 1 = e^-1 oE f -> e = f.
  Proof.
    intro h.
    refine ((ecompose_e1 _)^ @ ap (fun ef => e oE ef) h @ ecompose_e_Ve _ _).
  Defined.

  Definition emoveR_1M {A B} (e f : A <~> B)
  : 1 = f oE e^-1 -> e = f.
  Proof.
    intro h.
    refine ((ecompose_1e _)^ @ ap (fun fe => fe oE e) h @ ecompose_eV_e _ _).
  Defined.

  Definition emoveR_1V {A B} (e : A <~> B) (f : B <~> A)
  : 1 = f oE e -> e^-1 = f.
  Proof.
    intro h.
    refine ((ecompose_1e _)^ @ ap (fun fe => fe oE e^-1) h @ ecompose_ee_V _ _).
  Defined.

  Definition emoveR_V1 {A B} (e : A <~> B) (f : B <~> A)
  : 1 = e oE f -> e^-1 = f.
  Proof.
    intro h.
    refine ((ecompose_e1 _)^ @ ap (fun ef => e^-1 oE ef) h @ ecompose_V_ee _ _).
  Defined.

  (** We could package these up into tactics, much the same as the [with_rassoc] and [rewrite_move*] of [PathGroupoids.v].  I have not done so yet because there is currently no place where we would use these tactics.  If there is a use case, they are easy enough to copy from [PathGroupoids.v]. *)
End AssumeFunext.
