(* -*- mode: coq; mode: visual-line -*- *)

(** * Homotopy coequalizers *)

Require Import HoTT.Basics UnivalenceImpliesFunext.
Require Import Types.Paths Types.Forall Types.Sigma Types.Arrow Types.Universe.
Local Open Scope path_scope.

Module Export Coeq.

  Private Inductive Coeq {B A : Type} (f g : B -> A) : Type :=
  | coeq : A -> Coeq f g.

  Arguments coeq {B A f g} a.

  Axiom cp : forall {B A f g} (b:B), @coeq B A f g (f b) = coeq (g b).

  Definition Coeq_ind {B A f g} (P : @Coeq B A f g -> Type)
             (coeq' : forall a, P (coeq a))
             (cp' : forall b, (cp b) # (coeq' (f b)) = coeq' (g b))
  : forall w, P w
    := fun w => match w with coeq a => fun _ => coeq' a end cp'.

  Axiom Coeq_ind_beta_cp
  : forall {B A f g} (P : @Coeq B A f g -> Type)
           (coeq' : forall a, P (coeq a))
           (cp' : forall b, (cp b) # (coeq' (f b)) = coeq' (g b)) (b:B),
      apD (Coeq_ind P coeq' cp') (cp b) = cp' b.

End Coeq.

Definition Coeq_rec {B A f g} (P : Type) (coeq' : A -> P)
  (cp' : forall b, coeq' (f b) = coeq' (g b))
  : @Coeq B A f g -> P
  := Coeq_ind (fun _ => P) coeq' (fun b => transport_const _ _ @ cp' b).

Definition Coeq_rec_beta_cp {B A f g} (P : Type) (coeq' : A -> P)
  (cp' : forall b:B, coeq' (f b) = coeq' (g b)) (b:B)
  : ap (Coeq_rec P coeq' cp') (cp b) = cp' b.
Proof.
  unfold Coeq_rec.
  (** Use [eapply] rather than [refine] so that we don't get evars as goals, and don't have to shelve any goals with [shelve_unifiable]. *)
  eapply (cancelL (transport_const (cp b) _)).
  refine ((apD_const (@Coeq_ind B A f g (fun _ => P) coeq' _) (cp b))^ @ _).
  refine (Coeq_ind_beta_cp (fun _ => P) _ _ _).
Defined.

(** ** A double recursion principle *)

Section CoeqRec2.
  Context `{Funext}
          {B A : Type } {f g : B -> A} {B' A' : Type} {f' g' : B' -> A'}
          (P : Type) (coeq' : A -> A' -> P)
          (cpl : forall b a', coeq' (f b) a' = coeq' (g b) a')
          (cpr : forall a b', coeq' a (f' b') = coeq' a (g' b'))
          (cplr : forall b b', cpl b (f' b') @ cpr (g b) b'
                               = cpr (f b) b' @ cpl b (g' b')).

  Definition Coeq_rec2
  : Coeq f g -> Coeq f' g' -> P.
  Proof.
    refine (Coeq_rec _ _ _).
    - intros a.
      refine (Coeq_rec _ _ _).
      + intros a'.
        exact (coeq' a a').
      + intros b'; cbn.
        apply cpr.
    - intros b.
      apply path_arrow; intros a.
      revert a; refine (Coeq_ind _ _ _).
      + intros a'. cbn.
        apply cpl.
      + intros b'; cbn.
        refine (transport_paths_FlFr (cp b') (cpl b (f' b')) @ _).
        refine (concat_pp_p _ _ _ @ _).
        apply moveR_Vp.
        refine (_ @ cplr b b' @ _).
        * apply whiskerL.
          apply Coeq_rec_beta_cp.
        * apply whiskerR.
          symmetry; apply Coeq_rec_beta_cp.
  Defined.

  Definition Coeq_rec2_beta (a : A) (a' : A')
  : Coeq_rec2 (coeq a) (coeq a') = coeq' a a'
    := 1.

  Definition Coeq_rec2_beta_cpl (a : A) (b' : B')
  : ap (Coeq_rec2 (coeq a)) (cp b') = cpr a b'.
  Proof.
    apply Coeq_rec_beta_cp.
  Defined.

  Definition Coeq_rec2_beta_cpr (b : B) (a' : A')
  : ap (fun x => Coeq_rec2 x (coeq a')) (cp b) = cpl b a'.
  Proof.
    transitivity (ap10 (ap Coeq_rec2 (cp b)) (coeq a')).
    - refine (ap_compose Coeq_rec2 (fun h => h (coeq a')) _ @ _).
      apply ap_apply_l.
    - unfold Coeq_rec2; rewrite Coeq_rec_beta_cp.
      rewrite ap10_path_arrow.
      reflexivity.
  Defined.

  (** TODO: [Coeq_rec2_beta_cplr] *)

End CoeqRec2.

(** ** A double induction principle *)

Section CoeqInd2.
  Context `{Funext}
          {B A : Type } {f g : B -> A} {B' A' : Type} {f' g' : B' -> A'}
          (P : Coeq f g -> Coeq f' g' -> Type)
          (coeq' : forall a a', P (coeq a) (coeq a'))
          (cpl : forall b a',
                   transport (fun x => P x (coeq a')) (cp b)
                             (coeq' (f b) a') = coeq' (g b) a')
          (cpr : forall a b',
                   transport (fun y => P (coeq a) y) (cp b')
                             (coeq' a (f' b')) = coeq' a (g' b'))
          (** Perhaps this should really be written using [concatD]. *)
          (cplr : forall b b',
                  ap (transport (P (coeq (g b))) (cp b')) (cpl b (f' b'))
                  @ cpr (g b) b'
                  = transport_transport P (cp b) (cp b') (coeq' (f b) (f' b'))
                  @ ap (transport (fun x : Coeq f g => P x (coeq (g' b'))) (cp b))
                       (cpr (f b) b')
                  @ cpl b (g' b')).

  Definition Coeq_ind2
  : forall x y, P x y.
  Proof.
    refine (Coeq_ind _ _ _).
    - intros a.
      refine (Coeq_ind _ _ _).
      + intros a'.
        exact (coeq' a a').
      + intros b'; cbn.
        apply cpr.
    - intros b.
      apply path_forall; intros a.
      revert a; refine (Coeq_ind _ _ _).
      + intros a'. cbn.
        refine (transport_forall_constant _ _ _ @ _).
        apply cpl.
      + intros b'; cbn.
        refine (transport_paths_FlFr_D (cp b') _ @ _).
        rewrite Coeq_ind_beta_cp.
        (** Now begins the long haul. *)
        Open Scope long_path_scope.
        rewrite ap_pp.
        repeat rewrite concat_p_pp.
        (* Our first order of business is to get rid of the [Coeq_ind]s, which only occur in the following incarnation. *)
        set (G := (Coeq_ind (P (coeq (f b)))
                            (fun a' : A' => coeq' (f b) a')
                            (fun b'0 : B' => cpr (f b) b'0))).
        (* Let's reduce the [apD (loop # G)] first. *)
        rewrite (apD_transport_forall_constant P (cp b) G (cp b')); simpl.
        rewrite !inv_pp, !inv_V.
        (* Now we can cancel a [transport_forall_constant]. *)
        rewrite !concat_pp_p; apply whiskerL.
        (* And a path-inverse pair.  This removes all the [transport_forall_constant]s. *)
        rewrite !concat_p_pp, concat_pV_p.
        (* Now we can beta-reduce the last remaining [G]. *)
        subst G; rewrite Coeq_ind_beta_cp; simpl.
        (** Now we just have to rearrange it a bit. *)
        rewrite !concat_pp_p; do 2 apply moveR_Vp; rewrite !concat_p_pp.
        apply cplr.
        Close Scope long_path_scope.
  Qed.

End CoeqInd2.
