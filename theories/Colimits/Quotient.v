From HoTT Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import TruncType.
Require Import Colimits.GraphQuotient.
Require Import Truncations.Core.

Set Universe Minimization ToSet.

Local Open Scope path_scope.

(** * The set-quotient of a type by a relation

We aim to model:
<<
Inductive Quotient R : Type :=
   | class_of R : A -> Quotient R
   | qglue : forall x y, (R x y) -> class_of R x = class_of R y
   | ishset_quotient : IsHSet (Quotient R)
>>
We do this by defining the quotient as a 0-truncated graph quotient. 

Some results require additional assumptions, for example, that the relation be hprop-valued, or that the relation be reflexive, transitive or symmetric.

Throughout this file [a], [b] and [c] are elements of [A], [R] is a relation on [A], [x], [y] and [z] are elements of [Quotient R], [p] is a proof of [R a b].
*)

Definition Quotient@{i j k} {A : Type@{i}} (R : Relation@{i j} A) : Type@{k}
  := Trunc@{k} 0 (GraphQuotient@{i j k} R).

Definition class_of@{i j k} {A : Type@{i}} (R : Relation@{i j} A)
  : A -> Quotient@{i j k} R := tr o gq.

Definition qglue@{i j k} {A : Type@{i}} {R : Relation@{i j} A} {a b : A}
  : R a b -> class_of@{i j k} R a = class_of R b
  := fun p => ap tr (gqglue p).

Instance ishset_quotient {A : Type} (R : Relation A)
  : IsHSet (Quotient R) := _.

Definition Quotient_ind@{i j k l} {A : Type@{i}} (R : Relation@{i j} A)
  (P : Quotient@{i j k} R -> Type@{l}) {sP : forall x, IsHSet (P x)}
  (pclass : forall a, P (class_of R a))
  (peq : forall a b (H : R a b), qglue H # pclass a = pclass b)
  : forall x, P x.
Proof.
  rapply Trunc_ind; srapply GraphQuotient_ind.
  - exact pclass.
  - intros a b p.
    lhs napply (transport_compose P).
    exact (peq a b p).
Defined.

Definition Quotient_ind_beta_qglue@{i j k l}
  {A : Type@{i}} (R : Relation@{i j} A)
  (P : Quotient@{i j k} R -> Type@{l}) {sP : forall x, IsHSet (P x)}
  (pclass : forall a, P (class_of R a))
  (peq : forall a b (H : R a b), qglue H # pclass a = pclass b)
  (a b : A) (p : R a b)
  : apD (Quotient_ind@{i j k l} R P pclass peq) (qglue p) = peq a b p.
Proof.
  lhs napply apD_compose'.
  unfold Quotient_ind.
  nrefine (ap _ (GraphQuotient_ind_beta_gqglue _ pclass
    (fun a b p0 => transport_compose P tr _ _ @ peq a b p0) _ _ _) @ _).
  rapply concat_V_pp.
Defined.

Definition Quotient_rec@{i j k l}
  {A : Type@{i}} (R : Relation@{i j} A)
  (P : Type@{l}) `{IsHSet P} (pclass : A -> P)
  (peq : forall a b, R a b -> pclass a = pclass b)
  : Quotient@{i j k} R -> P.
Proof.
  srapply Trunc_rec; snapply GraphQuotient_rec.
  - exact pclass.
  - exact peq.
Defined.

Definition Quotient_rec_beta_qglue @{i j k l}
  {A : Type@{i}} (R : Relation@{i j} A)
  (P : Type@{l}) `{IsHSet P} (pclass : A -> P)
  (peq : forall a b, R a b -> pclass a = pclass b)
  (a b : A) (p : R a b)
  : ap (Quotient_rec@{i j k l} R P pclass peq) (qglue p) = peq a b p.
Proof.
  lhs_V napply (ap_compose tr).
  snapply GraphQuotient_rec_beta_gqglue.
Defined.

Arguments Quotient : simpl never.
Arguments class_of : simpl never.
Arguments qglue : simpl never.
Arguments Quotient_ind_beta_qglue : simpl never.
Arguments Quotient_rec_beta_qglue : simpl never.

Notation "A / R" := (Quotient (A:=A) R).

(** Quotient induction into an hprop. *)
Definition Quotient_ind_hprop {A : Type@{i}} (R : Relation@{i j} A)
  (P : A / R -> Type) `{forall x, IsHProp (P x)}
  (dclass : forall a, P (class_of R a))
  : forall x, P x.
Proof.
  srapply (Quotient_ind R P dclass).
  intros x y p; apply path_ishprop.
Defined.

Definition Quotient_ind2_hprop {A : Type@{i}} (R : Relation@{i j} A)
  (P : A / R -> A / R -> Type) `{forall x y, IsHProp (P x y)}
  (dclass : forall a b, P (class_of R a) (class_of R b))
  : forall x y, P x y.
Proof.
  intros x; srapply Quotient_ind_hprop; intros b.
  revert x; srapply Quotient_ind_hprop; intros a.
  exact (dclass a b).
Defined.

Definition Quotient_ind3_hprop {A : Type@{i}} (R : Relation@{i j} A)
  (P : A / R -> A / R -> A / R -> Type) `{forall x y z, IsHProp (P x y z)}
  (dclass : forall a b c, P (class_of R a) (class_of R b) (class_of R c))
  : forall x y z, P x y z.
Proof.
  intros x; srapply Quotient_ind2_hprop; intros b c.
  revert x; srapply Quotient_ind_hprop; intros a.
  exact (dclass a b c).
Defined.

Definition Quotient_ind2 {A : Type} (R : Relation A)
  (P : A / R -> A / R -> Type) `{forall x y, IsHSet (P x y)}
  (dclass : forall a b, P (class_of R a) (class_of R b))
  (dequiv_l : forall a a' b (p : R a a'),
    transport (fun x => P x _) (qglue p) (dclass a b) = dclass a' b)
  (dequiv_r : forall a b b' (p : R b b'), qglue p # dclass a b = dclass a b')
  : forall x y, P x y.
Proof.
  intro x.
  srapply Quotient_ind.
  - intro b.
    revert x.
    srapply Quotient_ind.
    + intro a.
      exact (dclass a b).
    + cbn beta.
      intros a a' p.
      by apply dequiv_l.
  - cbn beta.
    intros b b' p.
    revert x.
    srapply Quotient_ind_hprop; simpl.
    intro a; by apply dequiv_r.
Defined.

Definition Quotient_rec2 {A : Type} (R : Relation A) (B : Type) `{IsHSet B}
  (dclass : A -> A -> B)
  (dequiv_l : forall a a' b, R a a' -> dclass a b = dclass a' b)
  (dequiv_r : forall a b b', R b b' -> dclass a b = dclass a b')
  : A / R -> A / R -> B.
Proof.
  srapply Quotient_ind2.
  - exact dclass.
  - intros; lhs napply transport_const.
    by apply dequiv_l.
  - intros; lhs napply transport_const.
    by apply dequiv_r.
Defined.

Section Equiv.

  Context `{Univalence} {A : Type} (R : Relation A) `{is_mere_relation _ R}
    `{Transitive _ R} `{Symmetric _ R} `{Reflexive _ R}.

  (** The proposition of being in a given class in a quotient. This requires [Univalence] so that we know that [HProp] is a set. *)
  Definition in_class : A / R -> A -> HProp.
  Proof.
    intros x b; revert x.
    srapply Quotient_rec.
    1: intro a; exact (Build_HProp (R a b)).
    intros a c p; cbn beta.
    apply path_hprop.
    srapply equiv_iff_hprop; cbn.
    1: exact (transitivity (symmetry _ _ p)).
    exact (transitivity p).
  Defined.

  (** Being in a class is decidable if the relation is decidable. *)
  #[export] Instance decidable_in_class `{forall a b, Decidable (R a b)}
  : forall x a, Decidable (in_class x a).
  Proof.
    by srapply Quotient_ind_hprop.
  Defined.

  (** If [a] is in a class [x], then the class of [a] is equal to [x]. *)
  Lemma path_in_class_of : forall x a, in_class x a -> x = class_of R a.
  Proof.
    srapply Quotient_ind.
    { intros a b p.
      exact (qglue p). }
    intros a b p.
    funext ? ?.
    apply hset_path2.
  Defined.

  Lemma related_quotient_paths (a b : A)
    : class_of R a = class_of R b -> R a b.
  Proof.
    intros p.
    change (in_class (class_of R a) b).
    destruct p^.
    cbv; reflexivity.
  Defined.

  (** Theorem 10.1.8. *)
  Theorem path_quotient (a b : A)
    : R a b <~> (class_of R a = class_of R b).
  Proof.
    apply equiv_iff_hprop.
    - exact qglue.
    - apply related_quotient_paths.
  Defined.

  (** The map [class_of : A -> A/R] is a surjection. *)
  #[export] Instance issurj_class_of : IsSurjection (class_of R).
  Proof.
    apply BuildIsSurjection.
    srapply Quotient_ind_hprop.
    intro a.
    apply tr.
    by exists a.
  Defined.

  (** The universal property of the quotient.  This is Lemma 6.10.3. *)
  Theorem equiv_quotient_ump (B : Type) `{IsHSet B}
    : (A / R -> B) <~> {f : A -> B & forall a b, R a b -> f a = f b}.
  Proof.
    srapply equiv_adjointify.
    + intro f.
      exists (compose f (class_of R)).
      intros; f_ap.
      by apply qglue.
    + intros [f H'].
      exact (Quotient_rec _ _ _ H').
    + intros [f Hf].
      by apply equiv_path_sigma_hprop.
    + intros f.
      apply path_forall.
      srapply Quotient_ind_hprop.
      reflexivity.
  Defined.

(** TODO: The equivalence with VVquotient [A//R].
  10.1.10.
    Equivalence Relations are effective and there is an equivalence [A/R<~>A//R].

    This will need propositional resizing if we don't want to raise the universe level.
*)
(**
  The theory of canonical quotients is developed by C.Cohen:
  http://perso.crans.org/cohen/work/quotients/
 *)

End Equiv.

Section Functoriality.

  (* TODO: Develop a notion of set with Relation and use that instead of manually adding Relation preserving conditions. *)

  Definition Quotient_functor
    {A : Type} (R : Relation A)
    {B : Type} (S : Relation B)
    (f : A -> B) (fresp : forall a b, R a b -> S (f a) (f b))
    : Quotient R -> Quotient S.
  Proof.
    refine (Quotient_rec R _ (class_of S o f) _).
    intros a b p.
    apply qglue, fresp, p.
  Defined.

  Definition Quotient_functor_idmap
    {A : Type} {R : Relation A}
    : Quotient_functor R R idmap (fun x y => idmap) == idmap.
  Proof.
    by srapply Quotient_ind_hprop.
  Defined.

  Definition Quotient_functor_compose
    {A : Type} {R : Relation A}
    {B : Type} {S : Relation B}
    {C : Type} {T : Relation C}
    (f : A -> B) (fresp : forall a b, R a b -> S (f a) (f b))
    (g : B -> C) (gresp : forall a b, S a b -> T (g a) (g b))
    : Quotient_functor R T (g o f) (fun a b => (gresp _ _) o (fresp a b))
    == Quotient_functor S T g gresp o Quotient_functor R S f fresp.
  Proof.
    by srapply Quotient_ind_hprop.
  Defined.

  Context {A : Type} (R : Relation A)
          {B : Type} (S : Relation B).

  #[export] Instance isequiv_quotient_functor (f : A -> B)
    (fresp : forall a b, R a b <-> S (f a) (f b)) `{IsEquiv _ _ f}
    : IsEquiv (Quotient_functor R S f (fun a b => fst (fresp a b))).
  Proof.
    srapply (isequiv_adjointify _ (Quotient_functor S R f^-1 _)).
    { intros a b s.
      apply (snd (fresp _ _)).
      abstract (do 2 rewrite eisretr; exact s). }
    all: srapply Quotient_ind.
    + intros b; simpl.
      apply ap, eisretr.
    + intros; apply path_ishprop.
    + intros a; simpl.
      apply ap, eissect.
    + intros; apply path_ishprop.
  Defined.

  Definition equiv_quotient_functor (f : A -> B) `{IsEquiv _ _ f}
    (fresp : forall a b, R a b <-> S (f a) (f b))
    : Quotient R <~> Quotient S
    := Build_Equiv _ _ (Quotient_functor R S f (fun a b => fst (fresp a b))) _.

  Definition equiv_quotient_functor' (f : A <~> B)
    (fresp : forall a b, R a b <-> S (f a) (f b))
    : Quotient R <~> Quotient S
    := equiv_quotient_functor f fresp.

End Functoriality.

Section Kernel.

  (** ** Quotients of kernels of maps to sets give a surjection/mono factorization. *)

  (** Because the statement uses nested Sigma types, we need several variables to serve as [max] and [u+1]. We write [ar] for [max(a,r)], [ar'] for [ar+1], etc. *)
  Universes a r ar ar' b ab abr.
  Constraint a <= ar, r <= ar, ar < ar', a <= ab, b <= ab, ab <= abr, ar <= abr.

  Context `{Funext}.

  (** A function we want to factor. *)
  Context {A : Type@{a}} {B : Type@{b}} `{IsHSet B} (f : A -> B).

  (** A mere Relation equivalent to its kernel. *)
  Context (R : Relation@{a r} A)
          (is_ker : forall x y, f x = f y <~> R x y).

  (** The factorization theorem.  An advantage of stating it as one bundled result is that it is easier to state variations as we do below.  Disadvantages are that it requires more universe variables and that each piece of the answer depends on [Funext] and all of the universe variables, even when these aren't needed for that piece.  Below we will clean up the universe variables slightly, so we make this version [Local]. *)
  Local Definition quotient_kernel_factor_internal
    : exists (C : Type@{ar}) (e : A -> C) (m : C -> B),
      IsHSet C * IsSurjection e * IsEmbedding m * (f = m o e).
  Proof.
    exists (Quotient R).
    exists (class_of R).
    srefine (_;_).
    { refine (Quotient_ind R (fun _ => B) f _).
      intros x y p.
      lhs napply transport_const.
      exact ((is_ker x y)^-1 p). }
    repeat split; try exact _.
    intro u.
    apply hprop_allpath.
    intros [x q] [y p'].
    apply path_sigma_hprop; simpl.
    revert x y q p'.
    srapply Quotient_ind.
    2: intros; apply path_ishprop.
    intro a.
    srapply Quotient_ind.
    2: intros; apply path_ishprop.
    intros a' p p'.
    apply qglue, is_ker.
    exact (p @ p'^).
  Defined.

  (** We clean up the universe variables here, using only those declared in this Section. *)
  Definition quotient_kernel_factor_general@{|}
    := Eval unfold quotient_kernel_factor_internal in
      quotient_kernel_factor_internal@{ar' ar abr abr ab abr abr}.

End Kernel.

(** A common special case of [quotient_kernel_factor] is when we define [R] to be [f x = f y].  Then universes [r] and [b] are unified. *)
Definition quotient_kernel_factor@{a b ab ab' | a <= ab, b <= ab, ab < ab'}
  `{Funext} {A : Type@{a}} {B : Type@{b}} `{IsHSet B} (f : A -> B)
  : exists (C : Type@{ab}) (e : A -> C) (m : C -> B),
      IsHSet C * IsSurjection e * IsEmbedding m * (f = m o e).
Proof.
  exact (quotient_kernel_factor_general@{a b ab ab' b ab ab}
           f (fun a b => f a = f b) (fun x y => equiv_idmap)).
Defined.

(** If we use propositional resizing, we can replace [f x = f y] with a proposition [R x y] in universe [a], so that the universe of [C] is the same as the universe of [A]. *)
Definition quotient_kernel_factor_small@{a a' b ab | a < a', a <= ab, b <= ab}
  `{Funext} `{PropResizing}
  {A : Type@{a}} {B : Type@{b}} `{IsHSet B} (f : A -> B)
  : exists (C : Type@{a}) (e : A -> C) (m : C -> B),
      IsHSet C * IsSurjection e * IsEmbedding m * (f = m o e).
Proof.
  exact (quotient_kernel_factor_general@{a a a a' b ab ab}
           f (fun a b => smalltype@{a b} (f a = f b))
           (fun x y => (equiv_smalltype _)^-1%equiv)).
Defined.
