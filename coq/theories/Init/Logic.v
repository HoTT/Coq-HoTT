(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.

Require Export Notations.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

(** * Propositional connectives *)

(** [True] is the unit type. *)
Inductive True : Type :=
  I : True.

(** [False] is the empty type. *)
Inductive False : Type :=.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Type) : Type := A -> False.

Notation "~ x" := (not x) : type_scope.

Hint Unfold not: core.

(* (** Instead of eq we define paths. *) *)

(* Inductive paths (A : Type) (x : A) : A -> Type := *)
(*     idpath : x = x :> A *)

(* where *)

(* "x = y :> A" := (@paths A x y) : type_scope. *)

(* Notation "x = y" := (x = y :>_) : type_scope. *)
(* Notation "x <> y  :> T" := (~ x = y :>T) : type_scope. *)
(* Notation "x <> y" := (x <> y :>_) : type_scope. *)

(* Arguments paths {A} x _. *)
(* Arguments idpath {A x} , [A] x. *)

(* Arguments paths_ind [A] x P _ y _. *)
(* Arguments paths_rec [A] x P _ y _. *)
(* Arguments paths_rect [A] x P _ y _. *)

(* (** Paths can be reversed, moved here for the benefit of ssreflect. *) *)

(* Definition opposite {A} {x y : A} : (x = y) -> (y = x). *)
(* Proof. *)
(*   intros p. *)
(*   induction p. *)
(*   reflexivity. *)
(* Defined. *)

Hint Resolve I : core.

(* XXX: If add things below, such as eq_sym, Coq seems to use them secretly, which then breaks things.

Section Logic_lemmas.

  Theorem absurd : forall A C: Type, A -> ~ A -> C.
  Proof.
    unfold not; intros A C h1 h2.
    destruct (h2 h1).
  Qed.

  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
    Proof.
      destruct 1; trivial.
    Defined.
    Opaque eq_sym.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.
    Opaque eq_trans.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
      destruct 1; trivial.
    Defined.
    Opaque f_equal.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      red; intros h1 h2; apply h1; destruct h2; trivial.
    Qed.

  End equality.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.
End Logic_lemmas.

Module EqNotations.
  Notation "'rew' H 'in' H'" := (paths_rect _ _ H' _ H)
    (at level 10, H' at level 10).
(*  Notation "'rew' <- H 'in' H'" := (paths_rect_r _ H' H)
    (at level 10, H' at level 10). *)
  Notation "'rew' -> H 'in' H'" := (paths_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
End EqNotations.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Hint Immediate eq_sym not_eq_sym: core.
*)