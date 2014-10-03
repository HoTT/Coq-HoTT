Require Import HoTT.Basics.
Require Import types.Universe.
Require Import HSet HProp UnivalenceImpliesFunext.
Require Import hit.epi hit.Truncations hit.Connectedness.

Open Local Scope path_scope.
Open Local Scope equiv_scope.

(** ** Quotient of a Type by an hprop-valued relation

We aim to model:
<<
Inductive quotient : Type :=
   | class_of : A -> quotient
   | related_classes_eq : forall x y, (R x y), class_of x = class_of y
   | quotient_set : IsHSet quotient
>>
*)

(** This development should be further connected with the sections in the book; see below.*)

Module Export Quotient.

Section Domain.

Context {A : Type} (R:relation A) {sR: is_mere_relation R}.

(** We choose to let the definition of quotient depend on the proof that [R] is a set-relations.  Alternatively, we could have defined it for all relations and only develop the theory for set-relations.  The former seems more natural.

We do not require [R] to be an equivalence relation, but implicitly consider its transitive-reflexive closure. *)


(** Note: If we wanted to be really accurate, we'd need to put [@quotient A R sr] in the max [U_{sup(i, j)}] of the universes of [A : U_i] and [R : A -> A -> U_j].  But this requires some hacky code, at the moment, and the only thing we gain is avoiding making use of an implicit hpropositional resizing "axiom". *)

(** This definition has a parameter [sR] that shadows the ambient one in the Context in order to ensure that it actually ends up depending on everything in the Context when the section is closed, since its definition doesn't actually refer to any of them.  *)
Private Inductive quotient {sR: is_mere_relation R} : Type :=
  | class_of : A -> quotient.

(** The path constructors. *)
Axiom related_classes_eq : forall {x y : A}, R x y ->
 class_of x = class_of y.

Axiom quotient_set : IsHSet (@quotient sR).
Global Existing Instance quotient_set.

Definition quotient_rect (P : (@quotient sR) -> Type):
  forall dclass : forall x, P (class_of x),
  forall dequiv : (forall x y (H : R x y),
           transport _ (related_classes_eq H) (dclass x) = dclass y),
  forall q, P q.
Proof.
intros ? ? [a]. apply dclass.
Defined.

Definition quotient_rect_compute : forall {P} dclass dequiv x,
  quotient_rect P dclass dequiv (class_of x) = dclass x.
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

Context `{Univalence}.

Context {A : Type} (R : relation A) {sR: is_mere_relation R}
 {Htrans : Transitive R} {Hsymm : Symmetric R}.

Lemma quotient_path2 : forall {x y : quotient R} (p q : x=y), p=q.
Proof.
apply @set_path2. apply _.
Defined.

Definition in_class : quotient R -> A -> Type.
Proof.
apply (@quotient_rect _ _ _ (fun _ => A -> Type) R).
intros. eapply concat;[apply transport_const|].
apply path_forall. intro z. apply path_universe_uncurried. apply @equiv_iff_hprop; eauto.
Defined.

Context {Hrefl : Reflexive R}.

Lemma in_class_pr : forall x y, in_class (class_of R x) y = R x y.
Proof.
reflexivity.
Defined.

Global Instance in_class_is_prop : forall q x, IsHProp (in_class q x).
Proof.
apply (@quotient_rect A R _
    (fun q : quotient R => forall x, IsHProp (in_class q x)) (fun x y => transport _ (in_class_pr x y) (sR x y))).
intros. apply path_ishprop.
Defined.

Lemma quotient_rect_prop (P : quotient R -> hProp):
  forall dclass : forall x, P (class_of R x),
  forall q, P q.
Proof.
intros. apply (quotient_rect R P dclass).
intros. apply path_ishprop.
Defined.

Lemma class_of_repr : forall q x, in_class q x -> q = class_of R x.
Proof.
apply (@quotient_rect A R _
 (fun q : quotient R => forall x, in_class q x -> q = class_of _ x)
  (fun x y H => related_classes_eq R H)).
intros.
apply path_forall. intro z.
apply path_forall;intro H'.
apply quotient_path2.
Defined.

Lemma classes_eq_related : forall x y,
class_of R x = class_of R y -> R x y.
Proof.
intros x y H'.
pattern (R x y).
eapply transport. apply in_class_pr.
pattern (class_of R x). apply (transport _ (H'^)).
apply Hrefl.
Defined.

(** Thm 10.1.8 *)
Open Scope equiv_scope.
Theorem sets_exact : forall x y, (class_of R x = class_of R y) <~> R x y.
intros ??. apply equiv_iff_hprop.
 apply classes_eq_related.
apply related_classes_eq.
Defined.

Definition quotient_rect_nondep : forall {B : Type},
  forall dclass : (forall x : A, B),
  forall dequiv : (forall x y, R x y -> dclass x = dclass y),
  quotient R -> B.
Proof.
intros ? ? ?.
apply (quotient_rect R (fun _ : quotient _ => B)) with dclass.
intros ?? H'. destruct (related_classes_eq R H'). by apply dequiv.
Defined.

Definition quotient_rect_nondep2 {B : hSet} {dclass : (A -> A -> B)}:
  forall dequiv : (forall x x', R x x' -> forall y y',  R y y' ->
                  dclass x y = dclass x' y'),
  quotient R -> quotient R -> B.
Proof.
intro.
assert (dequiv0 : forall x x0 y : A, R x0 y -> dclass x x0 = dclass x y)
 by (intros ? ? ? Hx; apply dequiv;[apply Hrefl|done]).
refine (quotient_rect_nondep
  (fun x => quotient_rect_nondep (dclass x) (dequiv0 x)) _).
intros x x' Hx.
apply path_forall. red.
assert (dequiv1 : forall y : A,
  quotient_rect_nondep (dclass x) (dequiv0 x) (class_of _ y) =
  quotient_rect_nondep (dclass x') (dequiv0 x') (class_of _ y))
 by (intros; by apply dequiv).
refine (quotient_rect R (fun q =>
quotient_rect_nondep (dclass x) (dequiv0 x) q =
quotient_rect_nondep (dclass x') (dequiv0 x') q) dequiv1 _).
intros. apply iss.
Defined.

Definition quotient_ind : forall P : quotient R -> Type,
forall (Hprop' : forall x, IsHProp (P (class_of _ x))),
(forall x, P (class_of _ x)) -> forall y, P y.
Proof.
intros ? ? dclass. apply quotient_rect with dclass.
intros. apply Hprop'.
Defined.

(** From Ch6 *)
Theorem quotient_surjective: IsSurjection (class_of R).
Proof.
  apply BuildIsSurjection.
  apply (quotient_ind (fun y => merely (hfiber (class_of R) y))); try exact _.
  intro x. apply tr. by exists x.
Defined.

(** From Ch10 *)
Definition quotient_ump' (B:hSet): (quotient R -> B) ->
  (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))).
intro f. exists (compose f (class_of R) ).
intros. unfold compose. f_ap. by apply related_classes_eq.
Defined.

Definition quotient_ump'' (B:hSet): (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0)))
 -> quotient R -> B.
intros [f H'].
apply (quotient_rect_nondep _ H').
Defined.

Theorem quotient_ump (B:hSet): (quotient R -> B) <~>
  (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))).
Proof.
refine (equiv_adjointify (quotient_ump' B) (quotient_ump'' B) _ _).
intros [f Hf].
- by apply equiv_path_sigma_hprop.
- intros f.
  apply path_forall.
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

Section Kernel.

(** ** Quotients of kernels of maps to sets give a surjection/mono factorization. *)

Context {fs : Funext}.

(** A function we want to factor. *)
Context {A B : Type} `{IsHSet B} (f : A -> B).

(** A mere relation equivalent to its kernel. *)
Context (R : relation A) {sR : is_mere_relation R}.
Context (is_ker : forall x y, f x = f y <~> R x y).

Theorem quotient_kernel_factor
  : exists (C : Type) (e : A -> C) (m : C -> B),
      IsHSet C * IsSurjection e * IsEmbedding m * (f = m o e).
Proof.
  pose (C := quotient R).
  (* We put this explicitly in the context so that typeclass
  resolution will pick it up. *)
  assert (IsHSet C) by (unfold C; apply _).
  exists C.
  pose (e := class_of R).
  exists e.
  transparent assert (m : (C -> B)).
  { apply quotient_rect with f.
    intros x y H. transitivity (f x).
    - apply transport_const.
    - exact ((is_ker x y) ^-1 H). }
  exists m.
  split. split. split.
  - assumption.
  - apply quotient_surjective.
  - intro u.
    apply hprop_allpath.
    assert (H : forall (x y : C) (p : m x = u) (p' : m y = u), x = y).
    { refine (quotient_rect R _ _ _). intro a.
      refine (quotient_rect R _ _ _). intros a' p p'; fold e in p, p'.
      + apply related_classes_eq.
        refine (is_ker a a' _).
        change (m (e a) = m (e a')).
        exact (p @ p'^).
      + intros; apply path_ishprop.
      + intros; apply path_ishprop. }
    intros [x p] [y p'].
    apply path_sigma_hprop; simpl.
    exact (H x y p p').
  - reflexivity.
Defined.

End Kernel.
