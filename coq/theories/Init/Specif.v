(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*   This file has been modified for the purposes of the HoTT library.  *)
(************************************************************************)

(** Basic specifications : sets that may contain logical information *)

Set Implicit Arguments.

Require Import Notations.
Require Import Datatypes.
Local Open Scope identity_scope.
Require Import Logic.

(** In standard Coq, [sig] and [sig2] are defined as "subset types" which sum over predicates [P:A->Prop].  We don't use [Prop], so we never need them, but some parts of Coq (like [Program Definition]) expect them to be present.  So we include the definitions, but with [Prop] changed to [Type] to ensure that our code is not subtly polluted with [Prop]. *)

Inductive sig (A:Type) (P:A -> Type) : Type :=
    exist : forall x:A, P x -> sig P.

Inductive sig2 (A:Type) (P Q:A -> Type) : Type :=
    exist2 : forall x:A, P x -> Q x -> sig2 P Q.

(** Now we define the Sigma-types that we will actually use. *)

(** [(sigT A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sigT2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Inductive sigT (A:Type) (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Inductive sigT2 (A:Type) (P Q:A -> Type) : Type :=
    existT2 : forall x:A, P x -> Q x -> sigT2 P Q.

(* Notations *)

Arguments sigT (A P)%type.
Arguments sigT2 (A P Q)%type.

Notation  ex_intro := existT (only parsing).

Notation "{ x | P }" := (sigT (fun x => P)) : type_scope.
Notation "{ x | P & Q }" := (sigT2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A | P }" := (sigT (fun x:A => P)) : type_scope.
Notation "{ x : A | P & Q }" := (sigT2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (sigT2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (sigT2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

(* Definition exist := existT.  (* (only parsing). *) *)
(* Definition sig := sigT.  (* (only parsing). *) *)
(* Notation sig2 := (@sigT2 _) (only parsing). *)
(* Notation exist2 := (@existT2 _) (only parsing). *)

Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Notation "{ x : A  & P  & Q }" := (sigT2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.
(* Notation "{ x & P }" := (sigT (fun x:_ => P)) : type_scope. *)
(* Notation "{ x & P  & Q }" := (sigT2 (fun x:_ => P) (fun x:A => Q)) : *)
(*   type_scope. *)

Add Printing Let sigT.
Add Printing Let sigT2.


Definition proj1_sig (A : Type) (P : A -> Type) (hP : sigT P) : A :=
  match hP with existT x _ => x end.

(** Projections of [sig]

    An element [y] of a subset [{x:A | (P x)}] is the pair of an [a]
    of type [A] and of a proof [h] that [a] satisfies [P].  Then
    [(proj1_sig y)] is the witness [a] and [(proj2_sig y)] is the
    proof of [(P a)] *)

(** Projections of [sigT]

    An element [x] of a sigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(projT1 x)] is the first projection and [(projT2 x)] is the
    second projection, the type of which depends on the [projT1]. *)

Section Projections.

  Variable A : Type.
  Variable P : A -> Type.

  Definition projT1 (x:sigT P) : A := match x with
                                      | existT a _ => a
                                      end.
  Definition projT2 (x:sigT P) : P (projT1 x) :=
    match x return P (projT1 x) with
    | existT _ h => h
    end.

End Projections.

(** Various forms of the axiom of choice for specifications *)

Section Choice_lemmas.

  Variables S S' : Type.
  Variable R : S -> S' -> Type.
  Variable R' : S -> S' -> Type.
  Variables R1 R2 : S -> Type.

  Lemma Choice :
   (forall x:S, {y:S' & R' x y}) -> {f:S -> S' & forall z:S, R' z (f z)}.
  Proof.
    intro H.
    exists (fun z => projT1 (H z)).
    intro z; destruct (H z); assumption.
  Defined.

(*
  Lemma bool_choice :
   (forall x:S, (R1 x) + (R2 x)) ->
     {f:S -> bool & forall x:S, (f x = true) * (R1 x) + (f x = false) * R2 x}.
  Proof.
    intro H.
    exists (fun z:S => if H z then true else false).
    intro z; destruct (H z); auto.
  Defined.
*)

End Choice_lemmas.

Section Dependent_choice_lemmas.

  Variables X : Type.
  Variable R : X -> X -> Type.

  Lemma dependent_choice :
    (forall x:X, {y : _ & R x y}) ->
    forall x0, {f : nat -> X & (f O = x0) * (forall n, R (f n) (f (S n)))}.
  Proof.
    intros H x0.
    set (f:=fix f n := match n with O => x0 | S n' => projT1 (H (f n')) end).
    exists f.
    split. reflexivity.
    induction n; simpl; apply projT2.
  Defined.

End Dependent_choice_lemmas.


 (** A result of type [(Exc A)] is either a normal value of type [A] or
     an [error] :

     [Inductive Exc [A:Type] : Type := value : A->(Exc A) | error : (Exc A)].

     It is implemented using the option type. *)

Definition Exc := option.
Definition value := Some.
Definition error := @None.

Arguments error [A].

Definition except := False_rec. (* for compatibility with previous versions *)

Arguments except [P] _.

Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply False_rec.
  apply (h2 h1).
Defined.

Hint Resolve existT existT2: core.


(* Compatibility with ssreflect *)

(* Notation sigS := sigT (compat "8.2"). *)
Notation existS := existT (compat "8.2").
(* Notation sigS_rect := sigT_rect (compat "8.2"). *)
(* Notation sigS_rec := sigT_rec (compat "8.2"). *)
(* Notation sigS_ind := sigT_ind (compat "8.2"). *)
Notation projS1 := projT1 (compat "8.2").
Notation projS2 := projT2 (compat "8.2").

(* Notation sigS2 := sigT2 (compat "8.2"). *)
(* Notation existS2 := existT2 (compat "8.2"). *)
(* Notation sigS2_rect := sigT2_rect (compat "8.2"). *)
(* Notation sigS2_rec := sigT2_rec (compat "8.2"). *)
(* Notation sigS2_ind := sigT2_ind (compat "8.2"). *)

