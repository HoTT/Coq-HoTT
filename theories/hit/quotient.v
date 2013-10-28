Require Import HoTT.

Open Local Scope path_scope.

(** ** Quotient of a Type by a set-valued relation
We aim to model:
<<
Inductive quotient : Type :=
   | class_of : A -> quotient
   | class_of_path : forall x y, (R x y), class_of x = class_of y
>>
*)

(** This development should be further connected with the sections in the book;
see below.*)

(** We experiment with the unbundled approach to type classes. *)
Class setrel {A} (R:(relation A)):= issetrel:forall x y, IsHProp (R x y).

Module Export Quotient.

Section Domain.

Context {A : Type} {R:relation A} {sR:setrel R}.
(** We choose to let the definition of quotient depend on the proof that [R] is a set-relations.
Alternatively, we could have defined it for all relations and only develop the theory for set-relations.
The former seems more natural.

We do not require [R] to be an equivalence relation, but implicitly consider its transitive-reflexive closure. *)


Local Inductive quotient (sR:setrel R): Type :=
  | class_of : A -> quotient sR.
Axiom related_classes_eq : forall {x y : A}, R x y ->
 class_of _ x = class_of _ y.

Axiom quotient_set : IsHSet (quotient _).
Global Existing Instance quotient_set.

Definition quotient_rect (P : (quotient _)-> Type):
  forall dclass : forall x, P (class_of _ x),
  forall dequiv : (forall x y (H : R x y),
           transport _ (related_classes_eq H) (dclass x) = dclass y),
  forall q, P q.
Proof.
intros ? ? [a]. apply dclass.
Defined.

Definition quotient_rect_compute : forall {P} dclass dequiv x,
  quotient_rect P dclass dequiv (class_of _ x) = dclass x.
Proof.
reflexivity.
Defined.

(** Again equality of paths needs to be postulated *)
Axiom quotient_rect_compute_path : forall P dclass dequiv,
forall x y (H : R x y),
apD (quotient_rect P dclass dequiv) (related_classes_eq H)
 = dequiv x y H.

End Domain.

End Quotient.

Section Equiv.

Context {funext : Funext} {uni : Univalence}.

Context {A : Type} {R : relation A} {sR:setrel R}
 {Htrans : Transitive R} {Hsymm : Symmetric R}.
Hint Resolve sR : typeclass_instances.

Lemma quotient_path2 : forall {x y : quotient _} (p q : x=y), p=q.
Proof.
apply @set_path2. apply _.
Defined.

Definition in_class : quotient _ -> A -> Type.
Proof.
apply (@quotient_rect _ _ _ (fun _ => A -> Type) R).
intros. eapply concat;[apply transport_const|].
apply funext. intro z. apply uni. apply @equiv_iff_hprop; eauto.
Defined.

Context {Hrefl : Reflexive R}.

Lemma in_class_pr : forall x y, in_class (class_of _ x) y = R x y.
Proof.
reflexivity.
Defined.

Global Instance in_class_is_prop : forall q x, IsHProp (in_class q x).
Proof.
apply (@quotient_rect A R _
    (fun q : quotient sR => forall x, IsHProp (in_class q x)) (fun x y => transport _ (in_class_pr x y) (sR x y))).
intros. apply allpath_hprop.
Defined.

Require Import HProp.

Lemma quotient_rect_prop (P : quotient _ -> hProp):
  forall dclass : forall x, P (class_of _ x),
  forall q, P q.
Proof.
intros. apply (quotient_rect P dclass).
intros. apply allpath_hprop.
Defined.

Lemma class_of_repr : forall q x, in_class q x -> q = class_of _ x.
Proof.
apply (@quotient_rect A R _
 (fun q : quotient sR => forall x, in_class q x -> q = class_of _ x)
  (fun x y H => related_classes_eq H)).
intros.
apply funext. intro z.
apply funext;intro H'.
apply quotient_path2.
Defined.

Lemma classes_eq_related : forall x y,
class_of _ x = class_of _ y -> R x y.
Proof.
intros x y H.
pattern (R x y).
eapply transport. apply in_class_pr.
pattern (class_of _ x). apply (transport _ (H^)).
apply Hrefl.
Defined.

(** Thm 10.1.8 *)
Open Scope equiv_scope.
Theorem sets_exact : forall x y, (class_of _ x = class_of _ y) <~> R x y.
intros ??. apply equiv_iff_hprop.
 apply classes_eq_related.
apply related_classes_eq.
Defined.

Definition quotient_rect_nondep : forall {B : Type},
  forall dclass : (forall x : A, B),
  forall dequiv : (forall x y, R x y -> dclass x = dclass y),
  quotient _ -> B.
Proof.
intros ? ? ?.
apply (quotient_rect (fun _ : quotient _ => B)) with dclass.
intros ?? H. destruct (related_classes_eq H). by apply dequiv.
Defined.

Definition quotient_rect_nondep2 {B : hSet} {dclass : (A -> A -> B)}:
  forall dequiv : (forall x x', R x x' -> forall y y',  R y y' ->
                  dclass x y = dclass x' y'),
  quotient _ -> quotient _ -> B.
Proof.
intro.
assert (dequiv0 : forall x x0 y : A, R x0 y -> dclass x x0 = dclass x y)
 by (intros ? ? ? Hx; apply dequiv;[apply Hrefl|done]).
refine (quotient_rect_nondep
  (fun x => quotient_rect_nondep (dclass x) (dequiv0 x)) _).
intros x x' Hx.
apply funext. red.
assert (dequiv1 : forall y : A,
  quotient_rect_nondep (dclass x) (dequiv0 x) (class_of _ y) =
  quotient_rect_nondep (dclass x') (dequiv0 x') (class_of _ y))
 by (intros; by apply dequiv).
refine (quotient_rect (fun q =>
quotient_rect_nondep (dclass x) (dequiv0 x) q =
quotient_rect_nondep (dclass x') (dequiv0 x') q) dequiv1 _).
intros. apply iss.
Defined.

Definition quotient_ind : forall P : quotient _ -> Type,
forall (Hprop' : forall x, IsHProp (P (class_of _ x))),
(forall x, P (class_of _ x)) -> forall y, P y.
Proof.
intros ? ? dclass. apply quotient_rect with dclass.
intros. apply Hprop'.
Defined.

Require Import hit.epi minus1Trunc.

(** From Ch6 *)
Theorem  quotient_surjective: issurj (class_of _).
unfold issurj. apply (quotient_ind (fun y => hexists (fun x : A => class_of sR x = y))).
 apply _.
intro x. apply min1. by exists x.
Defined.

(** From Ch10 *)
Definition quotient_ump' (B:hSet): (quotient _ -> B) ->
  (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))).
intro f. exists (compose f (class_of sR) ).
intros. unfold compose. f_ap. by apply related_classes_eq.
Defined.

Definition quotient_ump'' (B:hSet): (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0)))
 -> quotient _ -> B.
intros [f H].
apply (quotient_rect_nondep _ H).
Defined.

Require Import Misc.
Theorem quotient_ump (B:hSet): (quotient _ -> B) <~>
  (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))).
Proof.
refine (equiv_adjointify (quotient_ump' B) (quotient_ump'' B) _ _).
intros [f Hf].
- by apply equiv_path_sigma_hprop.
- intros f.
  apply funext.
  red. apply quotient_ind;[apply _|reflexivity].
Defined.

(** Missing

The equivalence with VVquotient A//R.

This should lead to the unnamed theorem:
10.1.10. Equivalence relations are effective and there is an equivalence A/R<~>A//R. *)

(**
The theory of canonical quotients is developed by C.Cohen:
http://perso.crans.org/cohen/work/quotients/
*)

End Equiv.
