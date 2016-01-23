(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics.
Require Import Types.Universe Types.Arrow Types.Sigma.
Require Import HSet HProp UnivalenceImpliesFunext TruncType.
Require Import hit.epi hit.Truncations hit.Connectedness.

Local Open Scope path_scope.

(** * Quotient of a Type by an hprop-valued relation

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

    Context {A : Type} (R:relation A) {sR: is_mere_relation _ R}.

    (** We choose to let the definition of quotient depend on the proof that [R] is a set-relations.  Alternatively, we could have defined it for all relations and only develop the theory for set-relations.  The former seems more natural.

We do not require [R] to be an equivalence relation, but implicitly consider its transitive-reflexive closure. *)


    (** Note: If we wanted to be really accurate, we'd need to put [@quotient A R sr] in the max [U_{sup(i, j)}] of the universes of [A : U_i] and [R : A -> A -> U_j].  But this requires some hacky code, at the moment, and the only thing we gain is avoiding making use of an implicit hpropositional resizing "axiom". *)

    (** This definition has a parameter [sR] that shadows the ambient one in the Context in order to ensure that it actually ends up depending on everything in the Context when the section is closed, since its definition doesn't actually refer to any of them.  *)
    Private Inductive quotient {sR: is_mere_relation _ R} : Type :=
    | class_of : A -> quotient.

    (** The path constructors. *)
    Axiom related_classes_eq
    : forall {x y : A}, R x y ->
                        class_of x = class_of y.

    Axiom quotient_set : IsHSet (@quotient sR).
    Global Existing Instance quotient_set.

    Definition quotient_ind (P : (@quotient sR) -> Type) {sP : forall x, IsHSet (P x)}
               (dclass : forall x, P (class_of x))
               (dequiv : (forall x y (H : R x y), (related_classes_eq H) # (dclass x) = dclass y))
    : forall q, P q
      := fun q => match q with class_of a => fun _ _ => dclass a end sP dequiv.

    Definition quotient_ind_compute {P sP} dclass dequiv x
    : @quotient_ind P sP dclass dequiv (class_of x) = dclass x.
    Proof.
      reflexivity.
    Defined.

    (** Again equality of paths needs to be postulated *)
    Axiom quotient_ind_compute_path
    : forall P sP dclass dequiv,
      forall x y (H : R x y),
        apD (@quotient_ind P sP dclass dequiv) (related_classes_eq H)
        = dequiv x y H.

  End Domain.

End Quotient.

Section Equiv.

  Context `{Univalence}.

  Context {A : Type} (R : relation A) {sR: is_mere_relation _ R}
          {Htrans : Transitive R} {Hsymm : Symmetric R}.

  Lemma quotient_path2 : forall {x y : quotient R} (p q : x=y), p=q.
  Proof.
    apply @set_path2. apply _.
  Defined.

  Definition in_class : quotient R -> A -> hProp.
  Proof.
    refine (quotient_ind R (fun _ => A -> hProp) (fun a b => BuildhProp (R a b)) _).
    intros. eapply concat;[apply transport_const|].
    apply path_forall. intro z. apply path_hprop; simpl.
    apply @equiv_iff_hprop; eauto.
  Defined.

  Context {Hrefl : Reflexive R}.

  Lemma in_class_pr : forall x y, (in_class (class_of R x) y : Type) = R x y.
  Proof.
    reflexivity.
  Defined.

  Lemma quotient_ind_prop (P : quotient R -> Type)
        `{forall x, IsHProp (P x)} :
    forall dclass : forall x, P (class_of R x),
    forall q, P q.
  Proof.
    intros. apply (quotient_ind R P dclass).
    intros. apply path_ishprop.
  Defined.

  Global Instance decidable_in_class `{forall x y, Decidable (R x y)}
  : forall x a, Decidable (in_class x a).
  Proof.
    refine (quotient_ind_prop _ _).
    intros a b; exact (transport Decidable (in_class_pr a b) _).
  Defined.

  Lemma class_of_repr : forall q x, in_class q x -> q = class_of R x.
  Proof.
    apply (quotient_ind R
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
  Theorem sets_exact : forall x y, (class_of R x = class_of R y) <~> R x y.
    intros ??. apply equiv_iff_hprop.
    apply classes_eq_related.
    apply related_classes_eq.
  Defined.

  Definition quotient_rec {B : Type} {sB : IsHSet B}
             (dclass : (forall x : A, B))
             (dequiv : (forall x y, R x y -> dclass x = dclass y))
  : quotient R -> B.
  Proof.
    apply (quotient_ind R (fun _ : quotient _ => B)) with dclass.
    intros ?? H'. destruct (related_classes_eq R H'). by apply dequiv.
  Defined.

  Definition quotient_rec2 {B : hSet} {dclass : (A -> A -> B)}:
    forall dequiv : (forall x x', R x x' -> forall y y',  R y y' ->
                                                          dclass x y = dclass x' y'),
      quotient R -> quotient R -> B.
  Proof.
    intro.
    assert (dequiv0 : forall x x0 y : A, R x0 y -> dclass x x0 = dclass x y)
      by (intros ? ? ? Hx; apply dequiv;[apply Hrefl|done]).
    refine (quotient_rec
              (fun x => quotient_rec (dclass x) (dequiv0 x)) _).
    intros x x' Hx.
    apply path_forall. red.
    assert (dequiv1 : forall y : A,
                        quotient_rec (dclass x) (dequiv0 x) (class_of _ y) =
                        quotient_rec (dclass x') (dequiv0 x') (class_of _ y))
      by (intros; by apply dequiv).
    refine (quotient_ind R (fun q =>
                              quotient_rec (dclass x) (dequiv0 x) q =
                              quotient_rec (dclass x') (dequiv0 x') q) dequiv1 _).
    intros. apply path_ishprop.
  Defined.

  Definition quotient_ind_prop' : forall P : quotient R -> Type,
                                  forall (Hprop' : forall x, IsHProp (P (class_of _ x))),
                                    (forall x, P (class_of _ x)) -> forall y, P y.
  Proof.
    intros ? ? dclass. apply quotient_ind with dclass.
    - simple refine (quotient_ind R (fun x => IsHSet (P x)) _ _); cbn beta; try exact _.
      intros; apply path_ishprop.
    - intros. apply Hprop'.
  Defined.

  (** From Ch6 *)
  Theorem quotient_surjective: IsSurjection (class_of R).
  Proof.
    apply BuildIsSurjection.
    apply (quotient_ind_prop (fun y => merely (hfiber (class_of R) y))); try exact _.
    intro x. apply tr. by exists x.
  Defined.

  (** From Ch10 *)
  Definition quotient_ump' (B:hSet): (quotient R -> B) ->
                                     (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))).
    intro f. exists (compose f (class_of R) ).
    intros. f_ap. by apply related_classes_eq.
  Defined.

  Definition quotient_ump'' (B:hSet): (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0)))
                                      -> quotient R -> B.
    intros [f H'].
    apply (quotient_rec _ H').
  Defined.

  Theorem quotient_ump (B:hSet): (quotient R -> B) <~>
                                                   (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))).
  Proof.
    refine (equiv_adjointify (quotient_ump' B) (quotient_ump'' B) _ _).
    intros [f Hf].
    - by apply equiv_path_sigma_hprop.
    - intros f.
      apply path_forall.
      red. apply quotient_ind_prop';[apply _|reflexivity].
  Defined.

  (** Missing

  The equivalence with VVquotient [A//R].

  This should lead to the unnamed theorem:

  10.1.10. Equivalence relations are effective and there is an equivalence [A/R<~>A//R]. *)

  (**
  The theory of canonical quotients is developed by C.Cohen:
  http://perso.crans.org/cohen/work/quotients/
 *)

End Equiv.

Section Functoriality.

  Definition quotient_functor
             {A : Type} (R : relation A) {sR: is_mere_relation _ R}
             {B : Type} (S : relation B) {sS: is_mere_relation _ S}
             (f : A -> B) (fresp : forall x y, R x y -> S (f x) (f y))
  : quotient R -> quotient S.
  Proof.
    refine (quotient_rec R (class_of S o f) _).
    intros x y r.
    apply related_classes_eq, fresp, r.
  Defined.

  Context {A : Type} (R : relation A) {sR: is_mere_relation _ R}
          {B : Type} (S : relation B) {sS: is_mere_relation _ S}.

  Global Instance quotient_functor_isequiv
             (f : A -> B) (fresp : forall x y, R x y <-> S (f x) (f y))
             `{IsEquiv _ _ f}
  : IsEquiv (quotient_functor R S f (fun x y => fst (fresp x y))).
  Proof.
    simple refine (isequiv_adjointify _ (quotient_functor S R f^-1 _)
                               _ _).
    - intros u v s.
      apply (snd (fresp _ _)).
      abstract (do 2 rewrite eisretr; apply s).
    - intros x; revert x; simple refine (quotient_ind S _ _ _).
      + intros b; simpl. apply ap, eisretr.
      + intros; apply path_ishprop.
    - intros x; revert x; simple refine (quotient_ind R _ _ _).
      + intros a; simpl. apply ap, eissect.
      + intros; apply path_ishprop.
  Defined.

  Definition quotient_functor_equiv
             (f : A -> B) (fresp : forall x y, R x y <-> S (f x) (f y))
             `{IsEquiv _ _ f}
  : quotient R <~> quotient S
    := BuildEquiv _ _
         (quotient_functor R S f (fun x y => fst (fresp x y))) _.

  Definition quotient_functor_equiv'
             (f : A <~> B) (fresp : forall x y, R x y <-> S (f x) (f y))
  : quotient R <~> quotient S
    := quotient_functor_equiv f fresp.

End Functoriality.

Section Kernel.

  (** ** Quotients of kernels of maps to sets give a surjection/mono factorization. *)

  Context {fs : Funext}.

  (** A function we want to factor. *)
  Context {A B : Type} `{IsHSet B} (f : A -> B).

  (** A mere relation equivalent to its kernel. *)
  Context (R : relation A) {sR : is_mere_relation _ R}.
  Context (is_ker : forall x y, f x = f y <~> R x y).

  Theorem quotient_kernel_factor
  : exists (C : Type) (e : A -> C) (m : C -> B),
      IsHSet C * IsSurjection e * IsEmbedding m * (f = m o e).
  Proof.
    pose (C := quotient R).
    (* We put this explicitly in the context so that typeclass resolution will pick it up. *)
    assert (IsHSet C) by (unfold C; apply _).
    exists C.
    pose (e := class_of R).
    exists e.
    transparent assert (m : (C -> B)).
    { apply quotient_ind with f; try exact _.
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
      { simple refine (quotient_ind R _ _ _). intro a.
        simple refine (quotient_ind R _ _ _). intros a' p p'; fold e in p, p'.
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
