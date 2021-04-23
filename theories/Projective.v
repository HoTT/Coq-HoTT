Require Import Basics Types HProp HFiber HSet.
Require Import Truncations.
Require Import Modalities.Descent.
Require Import Modalities.Separated.
Require Import Modalities.Identity.
Require Import Limits.Pullback.


(** * Projective types *)

(** To quantify over all truncation levels including infinity, we parametrize [IsProjective] by a [Modality]. When specializing to [IsProjective purely] we get an (oo,-1)-projective predicate. When specializing to [IsProjective (Tr n)] we get an (n,-1)-projective predicate. *)

Definition IsProjective (O : Modality) (X : Type) : Type
  := forall A, In O A -> forall B, In O B ->
     forall f : X -> B, forall p : A -> B,
     IsSurjection p -> merely (exists s : X -> A, p o s == f).

(** An (oo,-1)-projective predicate [IsPureProjective]. *)

Notation IsPureProjective := (IsProjective purely).

(** An (n,-1)-projective predicate [IsTrProjective]. *)

Notation IsTrProjective n := (IsProjective (Tr n)).

(** A type X is projective if and only if surjections into X merely split. *)
Proposition iff_isprojective_surjections_split
  (O : Modality) (X : Type) `{In O X}
  : IsProjective O X <->
    (forall (Y : Type), In O Y -> forall (p : Y -> X),
          IsSurjection p -> merely (exists s : X -> Y, p o s == idmap)).
Proof.
  split.
  - intros isprojX Y oY p S; unfold IsProjective in isprojX.
    exact (isprojX Y _ X _ idmap p S).
  - intro splits. unfold IsProjective.
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

Corollary equiv_isprojective_surjections_split
  `{Funext} (O : Modality) (X : Type) `{In O X}
  : IsProjective O X <~>
    (forall (Y : Type), In O Y -> forall (p : Y -> X),
          IsSurjection p -> merely (exists s : X -> Y, p o s == idmap)).
Proof.
  exact (equiv_iff_hprop_uncurried (iff_isprojective_surjections_split O X)).
Defined.


(** ** Projectivity and the axiom of choice *)

(** In topos theory, an object X is said to be projective if the axiom of choice holds when making choices indexed by X. We will refer to this as [IsChoosable], to avoid confusion with [IsProjective] above. In similarity with [IsProjective], we parametrize it by a [Modality]. *)

Class IsChoosable (O : Modality) (A : Type) :=
  ischoosable :
    forall (B : A -> Type), (forall x, In O (B x)) ->
    (forall x, merely (B x)) -> merely (forall x, B x).

(** An (oo,-1)-choice predicate [IsPureChoosable]. *)

Notation IsPureChoosable := (IsChoosable purely).

(** An (n,-1)-choice predicate [IsTrChoosable]. *)

Notation IsTrChoosable n := (IsChoosable (Tr n)).

Global Instance ischoosable_sigma
  `{Funext} {A : Type} {B : A -> Type} (O : Modality)
  (chA : IsChoosable O A)
  (chB : forall a : A, IsChoosable O (B a))
  : IsChoosable O {a : A | B a}.
Proof.
  intros C sC f.
  set (f' := fun a => chB a (fun b => C (a; b)) _ (fun b => f (a; b))).
  specialize (chA (fun a => forall b, C (a; b)) _ f').
  strip_truncations.
  apply tr.
  intro.
  apply chA.
Qed.

Proposition iff_isprojective_ischoosable
  (O : Modality) (X : Type) `{In O X}
  : IsProjective O X <-> IsChoosable O X.
Proof.
  refine (iff_compose (iff_isprojective_surjections_split O X) _).
  split.
  - intros splits P oP S.
    specialize splits with {x : X & P x} pr1.
    pose proof (splits _ (fst (iff_merely_issurjection P) S)) as M.
    clear S splits.
    strip_truncations; apply tr.
    destruct M as [s p].
    intro x.
    exact (transport _ (p x) (s x).2).
  - intros choiceX Y oY p S.
    unfold IsConnMap, IsConnected in S.
    pose proof (fun b => (@center _ (S b))) as S'; clear S.
    pose proof (choiceX (hfiber p) _ S') as M; clear S'.
    strip_truncations; apply tr.
    exists (fun x => (M x).1).
    exact (fun x => (M x).2).
Defined.

Proposition equiv_isprojective_ischoosable
  `{Funext} (O : Modality) (X : Type) `{In O X}
  : IsProjective O X <~> IsChoosable O X.
Proof.
  nrapply (equiv_iff_hprop_uncurried
            (iff_isprojective_ischoosable O X)); try exact _.
  apply istrunc_forall.
Defined.

Proposition ispureprojective_unit : IsPureProjective Unit.
Proof.
  apply (iff_isprojective_ischoosable purely Unit).
  intros P trP S.
  specialize S with tt.
  strip_truncations; apply tr.
  apply Unit_ind.
  exact S.
Defined.

Section AC_oo_neg1.
  (** ** Projectivity and AC_(oo,-1) (defined in HoTT book, Exercise 7.8) *)
  (* TODO: Generalize to n, m. *)

  Context {AC : forall X : HSet, IsPureChoosable X}.

  (** (Exercise 7.9) Assuming AC_(oo,-1) every type merely has a projective cover. *)
  Proposition projective_cover_AC `{Univalence} (A : Type)
    : merely (exists X:HSet, exists p : X -> A, IsSurjection p).
  Proof.
    pose (X := Build_HSet (Tr 0 A)).
    pose proof ((equiv_isprojective_ischoosable _ X)^-1 (AC X)) as P.
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
    : IsPureProjective X <~> IsHSet X.
  Proof.
    apply equiv_iff_hprop.
    - intro isprojX. unfold IsProjective in isprojX.
      pose proof (projective_cover_AC X) as P; strip_truncations.
      destruct P as [P [p issurj_p]].
      pose proof (isprojX P _ X _ idmap p issurj_p) as S; strip_truncations.
      destruct S as [s h].
      rapply (istrunc_embedding_trunc s).
      apply isembedding_isinj_hset.
      exact (isinj_section h).
    - intro ishsetX.
      apply (equiv_isprojective_ischoosable purely X)^-1.
      rapply AC.
  Defined.

End AC_oo_neg1.
