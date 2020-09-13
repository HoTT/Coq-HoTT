Require Import Basics Types HProp HFiber HSet.
Require Import Truncations.
Require Import Modalities.Descent Modalities.Separated.
Require Import Limits.Pullback.


(** * Projective types *)

Definition IsProjective (X : Type) : Type
  := forall A B : Type, forall f : X -> B, forall p : A -> B,
        IsSurjection p -> merely (exists s : X -> A, p o s == f).

(** A type X is projective if and only if surjections into X merely split. *)
Proposition iff_isprojective_surjections_split (X : Type)
  : IsProjective X <->
    (forall (Y : Type), forall (p : Y -> X),
          IsSurjection p -> merely (exists s : X -> Y, p o s == idmap)).
Proof.
  split.
  - intros isprojX Y p S; unfold IsProjective in isprojX.
    exact (isprojX Y X idmap p S).
  - intro splits. unfold IsProjective.
    intros A B f p S.
    pose proof (splits (Pullback p f) pullback_pr2 _) as s'.
    strip_truncations.
    destruct s' as [s E].
    refine (tr (pullback_pr1 o s; _)).
    intro x.
    refine (pullback_commsq p f (s x) @ _).
    apply (ap f).
    apply E.
Defined.

Corollary equiv_isprojective_surjections_split `{Funext} (X : Type)
  : IsProjective X <~>
    (forall (Y : Type), forall (p : Y -> X),
          IsSurjection p -> merely (exists s : X -> Y, p o s == idmap)).
Proof.
  exact (equiv_iff_hprop_uncurried (iff_isprojective_surjections_split X)).
Defined.


(** ** Projectivity and the axiom of choice *)

(** In topos theory, an object X is said to be projective if the axiom of choice holds when making choices indexed by X. *)
Definition IsProjective' (X : Type) : Type := forall P : X -> Type,
    (forall x, merely (P x)) -> merely (forall x, P x).

Proposition iff_isprojective_choice (X : Type)
  : IsProjective X <-> IsProjective' X.
Proof.
  refine (iff_compose (iff_isprojective_surjections_split X) _).
  split.
  - intros splits P S.
    specialize splits with {x : X & P x} pr1.
    pose proof (splits (fst (iff_merely_issurjection P) S)) as M.
    clear S splits.
    strip_truncations; apply tr.
    destruct M as [s p].
    intro x.
    exact (transport _ (p x) (s x).2).
  - intros choiceX Y p S.
    unfold IsConnMap, IsConnected in S.
    pose proof (fun b => (@center _ (S b))) as S'; clear S.
    pose proof (choiceX (hfiber p) S') as M; clear S'.
    strip_truncations; apply tr.
    exists (fun x => (M x).1).
    exact (fun x => (M x).2).
Defined.

Proposition equiv_isprojective_choice `{Funext} (X : Type)
  : IsProjective X <~> IsProjective' X.
Proof.
  exact (equiv_iff_hprop_uncurried (iff_isprojective_choice X)).
Defined.

Proposition isprojective_unit : IsProjective Unit.
Proof.
  apply (iff_isprojective_choice Unit).
  intros P S.
  specialize S with tt.
  strip_truncations; apply tr.
  apply Unit_ind.
  exact S.
Defined.

Section AC_oo_neg1.
  (** ** Projectivity and AC_(oo,-1) (defined in HoTT book, Exercise 7.8) *)
  (* TODO: Generalize to n, m. *)

  Context {AC : forall X : hSet, IsProjective' X}.

  (** (Exercise 7.9) Assuming AC_(oo,-1) every type merely has a projective cover. *)
  Proposition projective_cover_AC `{Univalence} (A : Type)
    : merely (exists X:hSet, exists p : X -> A, IsSurjection p).
  Proof.
    pose (X := BuildhSet (Tr 0 A)).
    pose proof ((equiv_isprojective_choice X)^-1 (AC X)) as P.
    pose proof (P A X idmap tr _) as F; clear P.
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
    - intro isprojX. unfold IsProjective in isprojX.
      pose proof (projective_cover_AC X) as P; strip_truncations.
      destruct P as [P [p issurj_p]].
      pose proof (isprojX P X idmap p issurj_p) as S; strip_truncations.
      destruct S as [s h].
      rapply (istrunc_embedding_trunc s).
      apply isembedding_isinj_hset.
      exact (isinj_section h).
    - intro ishsetX.
      apply (equiv_isprojective_choice X)^-1.
      rapply AC.
  Defined.

End AC_oo_neg1.
