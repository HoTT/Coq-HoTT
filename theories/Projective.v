From HoTT Require Import Basics Types.
Require Import Truncations.Core Truncations.SeparatedTrunc.
Require Import Modalities.Modality Modalities.Identity.
Require Import Limits.Pullback.

(** * Projective types *)

(** To quantify over all truncation levels including infinity, we parametrize [IsOProjective] by a [Modality]. When specializing to [IsOProjective purely] we get an (oo,-1)-projectivity predicate, [IsProjective]. When specializing to [IsOProjective (Tr n)] we get an (n,-1)-projectivity predicate, [IsTrProjective]. *)

Definition IsOProjective (O : Modality) (X : Type) : Type
  := forall A, In O A -> forall B, In O B ->
     forall f : X -> B, forall p : A -> B,
     IsSurjection p -> merely (exists s : X -> A, p o s == f).

(** (oo,-1)-projectivity. *)

Notation IsProjective := (IsOProjective purely).

(** (n,-1)-projectivity. *)

Notation IsTrProjective n := (IsOProjective (Tr n)).

(** A type X is projective if and only if surjections into X merely split. *)
Proposition iff_isoprojective_surjections_split
  (O : Modality) (X : Type) `{In O X}
  : IsOProjective O X <->
    (forall (Y : Type), In O Y -> forall (p : Y -> X),
          IsSurjection p -> merely (exists s : X -> Y, p o s == idmap)).
Proof.
  split.
  - intros isprojX Y oY p S; unfold IsOProjective in isprojX.
    exact (isprojX Y _ X _ idmap p S).
  - intro splits. unfold IsOProjective.
    intros A oA B oB f p S.
    pose proof (splits (Pullback p f) _ pullback_pr2 _) as s'.
    strip_truncations.
    destruct s' as [s E].
    refine (tr (pullback_pr1 o s; _)).
    intro x.
    refine (pullback_commsq p f (s x) @ _).
    apply (ap f).
    apply E.
Defined.

Corollary equiv_isoprojective_surjections_split
  `{Funext} (O : Modality) (X : Type) `{In O X}
  : IsOProjective O X <~>
    (forall (Y : Type), In O Y -> forall (p : Y -> X),
          IsSurjection p -> merely (exists s : X -> Y, p o s == idmap)).
Proof.
  exact (equiv_iff_hprop_uncurried (iff_isoprojective_surjections_split O X)).
Defined.

(** ** Projectivity and the axiom of choice *)

(** In topos theory, an object X is said to be projective if the axiom of choice holds when making choices indexed by X. We will refer to this as [HasOChoice], to avoid confusion with [IsOProjective] above. In similarity with [IsOProjective], we parametrize it by a [Modality]. *)

Class HasOChoice (O : Modality) (A : Type) :=
  hasochoice :
    forall (B : A -> Type), (forall x, In O (B x)) ->
    (forall x, merely (B x)) -> merely (forall x, B x).

(** (oo,-1)-choice. *)

Notation HasChoice := (HasOChoice purely).

(** (n,-1)-choice. *)

Notation HasTrChoice n := (HasOChoice (Tr n)).

Instance hasochoice_sigma
  `{Funext} {A : Type} {B : A -> Type} (O : Modality)
  (chA : HasOChoice O A)
  (chB : forall a : A, HasOChoice O (B a))
  : HasOChoice O {a : A | B a}.
Proof.
  intros C sC f.
  set (f' := fun a => chB a (fun b => C (a; b)) _ (fun b => f (a; b))).
  specialize (chA (fun a => forall b, C (a; b)) _ f').
  strip_truncations.
  apply tr.
  intro.
  apply chA.
Defined.

Proposition isoprojective_ochoice (O : Modality) (X : Type)
  : HasOChoice O X -> IsOProjective O X.
Proof.
  intros chX A ? B ? f p S.
  assert (g : merely (forall x:X, hfiber p (f x))).
  - rapply chX.
    intro x.
    exact (center _).
  - strip_truncations; apply tr.
    exists (fun x:X => pr1 (g x)).
    intro x.
    exact (g x).2.
Defined.

Proposition hasochoice_oprojective (O : Modality) (X : Type) `{In O X}
  : IsOProjective O X -> HasOChoice O X.
Proof.
  refine (_ o fst (iff_isoprojective_surjections_split O X)).
  intros splits P oP S.
  specialize splits with {x : X & P x} pr1.
  pose proof (splits _ (fst (iff_merely_issurjection P) S)) as M.
  clear S splits.
  strip_truncations; apply tr.
  destruct M as [s p].
  intro x.
  exact (transport _ (p x) (s x).2).
Defined.

Proposition iff_isoprojective_hasochoice (O : Modality) (X : Type) `{In O X}
  : IsOProjective O X <-> HasOChoice O X.
Proof.
  split.
  - apply hasochoice_oprojective. exact _.
  - apply isoprojective_ochoice.
Defined.

Proposition equiv_isoprojective_hasochoice
  `{Funext} (O : Modality) (X : Type) `{In O X}
  : IsOProjective O X <~> HasOChoice O X.
Proof.
  refine (equiv_iff_hprop_uncurried (iff_isoprojective_hasochoice O X)).
  exact istrunc_forall.
Defined.

Proposition isprojective_unit : IsProjective Unit.
Proof.
  apply (isoprojective_ochoice purely Unit).
  intros P trP S.
  specialize S with tt.
  strip_truncations; apply tr.
  apply Unit_ind.
  exact S.
Defined.

Section AC_oo_neg1.
  (** ** Projectivity and AC_(oo,-1) (defined in HoTT book, Exercise 7.8) *)
  (* TODO: Generalize to n, m. *)

  Context {AC : forall X : HSet, HasChoice X}.

  (** (Exercise 7.9) Assuming AC_(oo,-1) every type merely has a projective cover. *)
  Proposition projective_cover_AC `{Univalence} (A : Type)
    : merely (exists X:HSet, exists p : X -> A, IsSurjection p).
  Proof.
    pose (X := Build_HSet (Tr 0 A)).
    pose proof ((equiv_isoprojective_hasochoice _ X)^-1 (AC X)) as P.
    pose proof (P A _ X _ idmap tr _) as F; clear P.
    strip_truncations.
    destruct F as [f p].
    refine (tr (X; (f; BuildIsSurjection f _))).
    intro a; unfold hfiber.
    apply equiv_O_sigma_O.
    refine (tr (tr a; _)).
    rapply (equiv_path_Tr _ _)^-1%equiv.  (* Uses Univalence. *)
    apply p.
  Defined.

  (** Assuming AC_(oo,-1), projective types are exactly sets. *)
  Theorem equiv_isprojective_ishset_AC `{Univalence} (X : Type)
    : IsProjective X <~> IsHSet X.
  Proof.
    apply equiv_iff_hprop.
    - intro isprojX. unfold IsOProjective in isprojX.
      pose proof (projective_cover_AC X) as P; strip_truncations.
      destruct P as [P [p issurj_p]].
      pose proof (isprojX P _ X _ idmap p issurj_p) as S; strip_truncations.
      exact (inO_retract_inO (Tr 0) X P S.1 p S.2).
    - intro ishsetX.
      apply (equiv_isoprojective_hasochoice purely X)^-1.
      rapply AC.
  Defined.

End AC_oo_neg1.
