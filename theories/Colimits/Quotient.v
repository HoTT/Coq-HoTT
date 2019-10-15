Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import HProp.
Require Import UnivalenceImpliesFunext.
Require Import TruncType.
Require Import HIT.epi.
Require Import HIT.Coeq.
Require Import Truncations.

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

Definition Quotient@{i j k} {A : Type@{i}} (R : relation@{i j} A)
  `{is_mere_relation _ R} : Type@{k}
  := Trunc@{k} 0 (Coeq@{k k}
    (fun x : sig@{k k} (fun a : A => sig (R a)) => x.1)
    (fun x : sig@{k k} (fun a : A => sig (R a)) => x.2.1)).

Definition class_of@{i j k} {A : Type@{i}} (R : relation@{i j} A)
  `{is_mere_relation _ R} : A -> Quotient@{i j k} R := tr o coeq.

Definition qglue@{i j k} {A : Type@{i}} {R : relation@{i j} A}
  `{is_mere_relation _ R} {x y : A}
  : R x y -> class_of@{i j k} R x = class_of R y
  := fun p => ap tr (cglue (x; y; p)).

Definition Quotient_ind@{i j k l}
  {A : Type@{i}} (R : relation@{i j} A) `{is_mere_relation _ R}
  (P : Quotient@{i j k} R -> Type@{l}) {sP : forall x, IsHSet (P x)}
  (pclass : forall x, P (class_of R x))
  (peq : forall x y (H : R x y), qglue H # pclass x = pclass y)
  : forall q, P q.
Proof.
  eapply Trunc_ind, Coeq_ind.
  1: assumption.
  intros [a [b p]].
  refine (transport_compose _ _ _ _ @ _).
  apply peq.
Defined.

Definition Quotient_ind_beta_qglue@{i j k l}
  {A : Type@{i}} (R : relation@{i j} A) `{is_mere_relation _ R}
  (P : Quotient@{i j k} R -> Type@{l}) {sP : forall x, IsHSet (P x)}
  (pclass : forall x, P (class_of R x))
  (peq : forall x y (H : R x y), qglue H # pclass x = pclass y)
  (x y : A) (p : R x y)
  : apD (Quotient_ind@{i j k l} R P pclass peq) (qglue p) = peq x y p.
Proof.
  refine (apD_compose' tr _ _ @ _).
  refine (ap _ (Coeq_ind_beta_cglue _ _ _ _) @ _).
  apply concat_V_pp.
Defined.

Definition Quotient_rec@{i j k l}
  {A : Type@{i}} (R : relation@{i j} A) `{is_mere_relation _ R}
  (P : Type@{l}) `{IsHSet P} (pclass : A -> P)
  (peq : forall x y, R x y -> pclass x = pclass y)
  : Quotient@{i j k} R -> P.
Proof.
  eapply Trunc_rec, Coeq_rec.
  intros [a [b p]].
  by apply peq.
Defined.

Definition Quotient_rec_beta_qglue @{i j k l}
  {A : Type@{i}} (R : relation@{i j} A) `{is_mere_relation _ R}
  (P : Type@{l}) `{IsHSet P} (pclass : A -> P)
  (peq : forall x y, R x y -> pclass x = pclass y)
  (x y : A) (p : R x y)
  : ap (Quotient_rec@{i j k l} R P pclass peq) (qglue p) = peq x y p.
Proof.
  refine ((ap_compose tr _ _)^ @ _).
  serapply Coeq_rec_beta_cglue.
Defined.

Arguments Quotient : simpl never.
Arguments class_of : simpl never.
Arguments qglue : simpl never.
Arguments Quotient_ind_beta_qglue : simpl never.
Arguments Quotient_rec_beta_qglue : simpl never.

(* TODO: add to Notations.v *)
Notation "A / R" := (Quotient (A:=A) R).

(*
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

End Quotient. *)

Section Equiv.

  Context `{Univalence} {A : Type} (R : relation A) `{is_mere_relation _ R}
    `{Transitive _ R} `{Symmetric _ R} `{Reflexive _ R}.

  (* The proposition of being in a given class in a quotient. *)
  Definition in_class : A / R -> A -> hProp.
  Proof.
    serapply Quotient_ind.
    { intros a b.
      exact (BuildhProp (R a b)). }
    intros x y p.
    refine (transport_const _ _ @ _).
    funext z.
    apply path_hprop.
    serapply equiv_iff_hprop; cbn.
    1: apply (transitivity (symmetry _ _ p)).
    apply (transitivity p).
  Defined.

  (* TODO: remove this since this is true by definition? *)
  (* If x is in the class of y then they are related. *)
  Definition in_class_of : forall x y, (in_class (class_of R x) y : Type) = R x y
    := ltac:(reflexivity).

  (* Quotient induction into a hprop. *)
  Definition Quotient_ind_hprop
    (P : Quotient R -> Type) `{forall x, IsHProp (P x)}
    (dclass : forall x, P (class_of R x)) : forall q, P q.
  Proof.
    serapply (Quotient_ind R P dclass).
    1: intro; apply trunc_succ.
    intros x y p.
    apply path_ishprop.
  Defined.

  (* Being in a class is decidable if the relation is decidable. *)
  Global Instance decidable_in_class `{forall x y, Decidable (R x y)}
  : forall x a, Decidable (in_class x a).
  Proof.
    by serapply Quotient_ind_hprop.
  Defined.

  (* if x is in a class q, then the class of x is equal to q. *)
  Lemma class_of_repr : forall q x, in_class q x -> q = class_of R x.
  Proof.
    serapply Quotient_ind.
    { intros x y p.
      apply (qglue p). }
    intros x y p.
    funext ? ?.
    apply hset_path2.
  Defined.

  Lemma related_quotient_paths : forall x y,
    class_of R x = class_of R y -> R x y.
  Proof.
    intros x y p.
    change (in_class (class_of R x) y).
    destruct p^.
    cbv; reflexivity.
  Defined.

  (** Thm 10.1.8 *)
  Theorem path_quotient : forall x y,
    R x y <~> (class_of R x = class_of R y).
  Proof.
    intros ??.
    apply equiv_iff_hprop.
    - apply qglue.
    - apply related_quotient_paths.
  Defined.

  Definition Quotient_rec2 `{Funext} {B : hSet} {dclass : A -> A -> B}
    {dequiv : forall x x', R x x' -> forall y y',
      R y y' -> dclass x y = dclass x' y'}
    : A / R -> A / R -> B.
  Proof.
    serapply Quotient_rec.
    { intro a.
      serapply Quotient_rec.
      { revert a.
        assumption. }
      by apply (dequiv a a). }
    intros x y p.
    apply path_forall.
    serapply Quotient_ind.
    { cbn; intro a.
      by apply dequiv. }
    intros a b q.
    apply path_ishprop.
  Defined.

  Definition Quotient_ind_hprop' (P : A / R -> Type)
    `{forall x, IsHProp (P (class_of _ x))}
    (dclass : forall x, P (class_of _ x)) : forall y, P y.
  Proof.
    apply Quotient_ind with dclass.
    { serapply Quotient_ind.
      1: intro; apply trunc_succ.
      intros ???; apply path_ishprop. }
    intros; apply path_ishprop.
  Defined.

  (** The map class_of : A -> A/R is a surjection. *)
  Global Instance issurj_class_of : IsSurjection (class_of R).
  Proof.
    apply BuildIsSurjection.
    serapply Quotient_ind_hprop.
    intro x.
    apply tr.
    by exists x.
  Defined.

  (* Universal property of quotient *)
  (* Lemma 6.10.3 *)
  Theorem equiv_quotient_ump (B : hSet)
    : (Quotient R -> B) <~> {f : A -> B & forall x y, R x y -> f x = f y}.
  Proof.
    serapply equiv_adjointify.
    + intro f.
      exists (compose f (class_of R)).
      intros; f_ap.
      by apply qglue.
    + intros [f H'].
      apply (Quotient_rec _ _ _ H').
    + intros [f Hf].
      by apply equiv_path_sigma_hprop.
    + intros f.
      apply path_forall.
      serapply Quotient_ind_hprop.
      reflexivity.
  Defined.

  (** TODO:

  The equivalence with VVquotient [A//R].

  This should lead to the unnamed theorem:

  10.1.10. Equivalence relations are effective and there is an equivalence [A/R<~>A//R].
  
  This will need propositional resizing if we don't want to raise the universe level. *)

  (**
  The theory of canonical quotients is developed by C.Cohen:
  http://perso.crans.org/cohen/work/quotients/
 *)

End Equiv.

Section Functoriality.

  Definition Quotient_functor
    {A : Type} (R : relation A) {sR : is_mere_relation _ R}
    {B : Type} (S : relation B) {sS : is_mere_relation _ S}
    (f : A -> B) (fresp : forall x y, R x y -> S (f x) (f y))
    : Quotient R -> Quotient S.
  Proof.
    refine (Quotient_rec R _ (class_of S o f) _).
    intros x y r.
    apply qglue, fresp, r.
  Defined.

  Definition Quotient_functor_idmap
    {A : Type} {R : relation A} {sR : is_mere_relation _ R}
    : Quotient_functor R R idmap (fun x y => idmap) == idmap.
  Proof.
    by serapply Quotient_ind_hprop.
  Defined.

  Definition Quotient_functor_compose
    {A : Type} {R : relation A} {sR : is_mere_relation _ R}
    {B : Type} {S : relation B} {sS : is_mere_relation _ S}
    {C : Type} {T : relation C} {sT : is_mere_relation _ T}
    (f : A -> B) (fresp : forall x y, R x y -> S (f x) (f y))
    (g : B -> C) (gresp : forall x y, S x y -> T (g x) (g y))
    : Quotient_functor R T (g o f) (fun x y => (gresp _ _) o (fresp x y))
    == Quotient_functor S T g gresp o Quotient_functor R S f fresp.
  Proof.
    by serapply Quotient_ind_hprop.
  Defined.

  Context {A : Type} (R : relation A) {sR : is_mere_relation _ R}
          {B : Type} (S : relation B) {sS : is_mere_relation _ S}.

  Global Instance isequiv_quotient_functor (f : A -> B)
    (fresp : forall x y, R x y <-> S (f x) (f y)) `{IsEquiv _ _ f}
    : IsEquiv (Quotient_functor R S f (fun x y => fst (fresp x y))).
  Proof.
    serapply (isequiv_adjointify _ (Quotient_functor S R f^-1 _)).
    { intros u v s.
      apply (snd (fresp _ _)).
      abstract (do 2 rewrite eisretr; apply s). }
    all: serapply Quotient_ind.
    + intros b; simpl.
      apply ap, eisretr.
    + intros; apply path_ishprop.
    + intros a; simpl.
      apply ap, eissect.
    + intros; apply path_ishprop.
  Defined.

  Definition equiv_quotient_functor (f : A -> B) `{IsEquiv _ _ f}
    (fresp : forall x y, R x y <-> S (f x) (f y))
    : Quotient R <~> Quotient S
    := BuildEquiv _ _ (Quotient_functor R S f (fun x y => fst (fresp x y))) _.

  Definition equiv_quotient_functor' (f : A <~> B)
    (fresp : forall x y, R x y <-> S (f x) (f y))
    : Quotient R <~> Quotient S
    := equiv_quotient_functor f fresp.

End Functoriality.

Section Kernel.

  (** ** Quotients of kernels of maps to sets give a surjection/mono factorization. *)

  Context `{Funext}.
  Universe i.

  (** A function we want to factor. *)
  Context {A : Type@{i}} {B : Type} `{IsHSet B} (f : A -> B).

  (** A mere relation equivalent to its kernel. *)
  Context (R : relation A) {sR : is_mere_relation _ R}
          (is_ker : forall x y, f x = f y <~> R x y).

  Theorem quotient_kernel_factor
    : exists (C : Type@{i}) (e : A -> C) (m : C -> B),
      IsHSet C * IsSurjection e * IsEmbedding m * (f = m o e).
  Proof.
    exists (Quotient R).
    exists (class_of R).
    srefine (_;_).
    { apply Quotient_ind with f; try exact _.
      intros x y p.
      transitivity (f x).
      - apply transport_const.
      - exact ((is_ker x y)^-1 p). }
    repeat split; try exact _.
    intro u.
    apply hprop_allpath.
    intros [x q] [y p'].
    apply path_sigma_hprop; simpl.
    revert x y q p'.
    serapply Quotient_ind.
    2: intros; apply path_ishprop.
    intro a.
    serapply Quotient_ind.
    2: intros; apply path_ishprop.
    intros a' p p'.
    apply qglue, is_ker.
    exact (p @ p'^).
  Defined.

End Kernel.
