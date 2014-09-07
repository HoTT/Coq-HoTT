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
Local Set Primitive Projections.

(** [(sig A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sig2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Record sig {A} (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P proj1_sig }.

(** We make the parameters maximally inserted so that we can pass around [pr1] as a function and have it actually mean "first projection" in, e.g., [ap]. *)

Arguments exist {A}%type P%type _ _.
Arguments proj1_sig {A P} _ / .
Arguments proj2_sig {A P} _ / .

Inductive sig2 (A:Type) (P Q:A -> Type) : Type :=
    exist2 : forall x:A, P x -> Q x -> sig2 P Q.

Arguments sig (A P)%type.
Arguments sig2 (A P Q)%type.

(** *** Notations *)

(** In standard Coq, [sig] and [sig2] are defined as "subset types" which sum over predicates [P:A->Prop], while [sigT] and [sigT2] are the [Type] variants.  Because we don't use [Prop], we combine the two versions, and make [sigT] a notation for [sig].  Note that some parts of Coq (like [Program Definition]) expect [sig] to be present. *)

Notation sigT := sig (only parsing).
Notation existT := exist (only parsing).
Notation sigT_rect := sig_rect (only parsing).
Notation sigT_rec := sig_rect (only parsing).
Notation sigT_ind := sig_rect (only parsing).
Notation sigT2 := sig2 (only parsing).
Notation existT2 := exist2 (only parsing).
Notation sigT2_rect := sig2_rect (only parsing).
Notation sigT2_rec := sig2_rect (only parsing).
Notation sigT2_ind := sig2_rect (only parsing).

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

Add Printing Let sig.
Add Printing Let sig2.


(** Projections of [sigT]

    An element [x] of a sigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(proj1 x)] is the first projection and [(proj2 x)] is the
    second projection, the type of which depends on the [proj1]. *)

Notation projT1 := proj1_sig (only parsing).
Notation projT2 := proj2_sig (only parsing).


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
