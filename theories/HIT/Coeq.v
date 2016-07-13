(* -*- mode: coq; mode: visual-line -*- *)

(** * Homotopy coequalizers *)

Require Import HoTT.Basics UnivalenceImpliesFunext.
Require Import Types.Paths Types.Forall Types.Sigma Types.Arrow Types.Universe.
Local Open Scope path_scope.

(** ** Definition *)

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

(** ** Functoriality *)

Definition functor_coeq {B A f g B' A' f' g'}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
: @Coeq B A f g -> @Coeq B' A' f' g'.
Proof.
  refine (Coeq_rec _ (coeq o k) _); intros b.
  refine (ap coeq (p b) @ _ @ ap coeq (q b)^).
  apply cp.
Defined.

Definition functor_coeq_beta_cp {B A f g B' A' f' g'}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
           (b : B)
: ap (functor_coeq h k p q) (cp b)
  = ap coeq (p b) @ cp (h b) @ ap coeq (q b)^
:= (Coeq_rec_beta_cp _ _ _ b).

Definition functor_coeq_compose {B A f g B' A' f' g' B'' A'' f'' g''}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
           (h' : B' -> B'') (k' : A' -> A'')
           (p' : k' o f' == f'' o h') (q' : k' o g' == g'' o h')
: functor_coeq (h' o h) (k' o k)
               (fun b => ap k' (p b) @ p' (h b))
               (fun b => ap k' (q b) @ q' (h b))
  == functor_coeq h' k' p' q' o functor_coeq h k p q.
Proof.
  refine (Coeq_ind _ (fun a => 1) _); cbn; intros b.
  rewrite transport_paths_FlFr.
  rewrite concat_p1; apply moveR_Vp; rewrite concat_p1.
  rewrite ap_compose.
  rewrite !functor_coeq_beta_cp, !ap_pp, functor_coeq_beta_cp.
  rewrite <- !ap_compose. cbn.
  rewrite !ap_V, ap_pp, inv_pp, <- ap_compose, !concat_p_pp.
  reflexivity.
Qed.

Definition functor_coeq_homotopy {B A f g B' A' f' g'}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
           (h' : B -> B') (k' : A -> A')
           (p' : k' o f == f' o h') (q' : k' o g == g' o h')
           (r : h == h') (s : k == k')
           (u : forall b, s (f b) @ p' b = p b @ ap f' (r b))
           (v : forall b, s (g b) @ q' b = q b @ ap g' (r b))
: functor_coeq h k p q == functor_coeq h' k' p' q'.
Proof.
  refine (Coeq_ind _ (fun a => ap coeq (s a)) _); cbn; intros b.
  refine (transport_paths_FlFr (cp b) _ @ _).
  rewrite concat_pp_p; apply moveR_Vp.
  rewrite !functor_coeq_beta_cp.
  Open Scope long_path_scope.
  rewrite !concat_p_pp.
  rewrite <- (ap_pp (@coeq _ _ f' g') (s (f b)) (p' b)).
  rewrite u, ap_pp, !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
  rewrite ap_V; apply moveR_pV.
  rewrite !concat_pp_p, <- (ap_pp (@coeq _ _ f' g') (s (g b)) (q' b)).
  rewrite v, ap_pp, ap_V, concat_V_pp.
  rewrite <- !ap_compose.
  exact (concat_Ap (@cp _ _ f' g') (r b)).
  Close Scope long_path_scope.
Qed.

Definition functor_coeq_sect {B A f g B' A' f' g'}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
           (h' : B' -> B) (k' : A' -> A)
           (p' : k' o f' == f o h') (q' : k' o g' == g o h')
           (r : Sect h h') (s : Sect k k')
           (u : forall b, ap k' (p b) @ p' (h b) @ ap f (r b) = s (f b))
           (v : forall b, ap k' (q b) @ q' (h b) @ ap g (r b) = s (g b))
: Sect (functor_coeq h k p q) (functor_coeq h' k' p' q').
Proof.
  refine (Coeq_ind _ (fun a => ap coeq (s a)) _); cbn; intros b.
  refine (transport_paths_FFlr (cp b) _ @ _).
  rewrite concat_pp_p; apply moveR_Vp.
  rewrite functor_coeq_beta_cp, !ap_pp.
  rewrite <- !ap_compose; cbn.
  rewrite functor_coeq_beta_cp.
  Open Scope long_path_scope.
  rewrite !concat_p_pp.
  rewrite <- u, !ap_pp, !(ap_compose k' coeq).
  rewrite !concat_pp_p; do 2 apply whiskerL.
  rewrite !concat_p_pp.
  rewrite <- v.
  rewrite !ap_pp, !ap_V, !concat_p_pp, !concat_pV_p.
  rewrite <- !ap_compose.
  exact (concat_Ap cp (r b)).
  Close Scope long_path_scope.
Qed.

Section IsEquivFunctorCoeq.

  Context {B A f g B' A' f' g'}
          (h : B -> B') (k : A -> A')
          `{IsEquiv _ _ h} `{IsEquiv _ _ k}
          (p : k o f == f' o h) (q : k o g == g' o h).

  Definition functor_coeq_inverse
  : @Coeq B' A' f' g' -> @Coeq B A f g.
  Proof.
    refine (functor_coeq h^-1 k^-1 _ _).
    - intros b.
      refine (ap (k^-1 o f') (eisretr h b)^ @ _ @ eissect k (f (h^-1 b))).
      apply ap, inverse, p.
    - intros b.
      refine (ap (k^-1 o g') (eisretr h b)^ @ _ @ eissect k (g (h^-1 b))).
      apply ap, inverse, q.
  Defined.

  Definition functor_coeq_eissect
  : Sect functor_coeq_inverse (functor_coeq h k p q).
  Proof.
    Open Scope long_path_scope.
    refine (functor_coeq_sect _ _ _ _ _ _ _ _
                              (eisretr h) (eisretr k) _ _); intros b.
    (** The two proofs are identical modulo replacing [f] by [g], [f'] by [g'], and [p] by [q]. *)
    all:rewrite !ap_pp, <- eisadj.
    all:rewrite <- !ap_compose.
    all:rewrite (concat_pA1_p (eisretr k) _ _).
    all:rewrite concat_pV_p.
    all:rewrite <- (ap_compose (k^-1 o _) k).
    all:rewrite (ap_compose _ (k o k^-1)).
    all:rewrite (concat_A1p (eisretr k) (ap _ (eisretr h b)^)).
    all:rewrite ap_V, concat_pV_p; reflexivity.
    Close Scope long_path_scope.
  Qed.

  Definition functor_coeq_eisretr
  : Sect (functor_coeq h k p q) functor_coeq_inverse.
  Proof.
    Open Scope long_path_scope.
    refine (functor_coeq_sect _ _ _ _ _ _ _ _
                              (eissect h) (eissect k) _ _); intros b.
    all:rewrite !concat_p_pp, eisadj, <- ap_V, <- !ap_compose.
    all:rewrite (ap_compose (_ o h) k^-1).
    all:rewrite <- !(ap_pp k^-1), !concat_pp_p.
    1:rewrite (concat_Ap (fun b => (p b)^) (eissect h b)^).
    2:rewrite (concat_Ap (fun b => (q b)^) (eissect h b)^).
    all:rewrite concat_p_Vp, concat_p_pp.
    all:rewrite <- (ap_compose (k o _) k^-1), (ap_compose _ (k^-1 o k)).
    all:rewrite (concat_A1p (eissect k) _).
    all:rewrite ap_V, concat_pV_p; reflexivity.
    Close Scope long_path_scope.
  Qed.

  Global Instance isequiv_functor_coeq
  : IsEquiv (functor_coeq h k p q)
    := isequiv_adjointify _ functor_coeq_inverse
                          functor_coeq_eissect functor_coeq_eisretr.

  Definition equiv_functor_coeq
  : @Coeq B A f g <~> @Coeq B' A' f' g'
    := BuildEquiv _ _ (functor_coeq h k p q) _.

End IsEquivFunctorCoeq.

Definition equiv_functor_coeq' {B A f g B' A' f' g'}
           (h : B <~> B') (k : A <~> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
: @Coeq B A f g <~> @Coeq B' A' f' g'
  := equiv_functor_coeq h k p q.

(** ** A double recursion principle *)

Section CoeqRec2.
  Context `{Funext}
          {B A : Type} {f g : B -> A} {B' A' : Type} {f' g' : B' -> A'}
          (P : Type) (coeq' : A -> A' -> P)
          (cpl : forall b a', coeq' (f b) a' = coeq' (g b) a')
          (cpr : forall a b', coeq' a (f' b') = coeq' a (g' b'))
          (cplr : forall b b', cpl b (f' b') @ cpr (g b) b'
                               = cpr (f b) b' @ cpl b (g' b')).

  Definition Coeq_rec2
  : Coeq f g -> Coeq f' g' -> P.
  Proof.
    simple refine (Coeq_rec _ _ _).
    - intros a.
      simple refine (Coeq_rec _ _ _).
      + intros a'.
        exact (coeq' a a').
      + intros b'; cbn.
        apply cpr.
    - intros b.
      apply path_arrow; intros a.
      revert a; simple refine (Coeq_ind _ _ _).
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
          {B A : Type} {f g : B -> A} {B' A' : Type} {f' g' : B' -> A'}
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
                  @ ap (transport (fun x => P x (coeq (g' b'))) (cp b))
                       (cpr (f b) b')
                  @ cpl b (g' b')).

  Definition Coeq_ind2
  : forall x y, P x y.
  Proof.
    simple refine (Coeq_ind _ _ _).
    - intros a.
      simple refine (Coeq_ind _ _ _).
      + intros a'.
        exact (coeq' a a').
      + intros b'; cbn.
        apply cpr.
    - intros b.
      apply path_forall; intros a.
      revert a; simple refine (Coeq_ind _ _ _).
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
        (** Our first order of business is to get rid of the [Coeq_ind]s, which only occur in the following incarnation. *)
        set (G := (Coeq_ind (P (coeq (f b)))
                            (fun a' : A' => coeq' (f b) a')
                            (fun b'0 : B' => cpr (f b) b'0))).
        (** Let's reduce the [apD (loop # G)] first. *)
        rewrite (apD_transport_forall_constant P (cp b) G (cp b')); simpl.
        rewrite !inv_pp, !inv_V.
        (** Now we can cancel a [transport_forall_constant]. *)
        rewrite !concat_pp_p; apply whiskerL.
        (** And a path-inverse pair.  This removes all the [transport_forall_constant]s. *)
        rewrite !concat_p_pp, concat_pV_p.
        (** Now we can beta-reduce the last remaining [G]. *)
        subst G; rewrite Coeq_ind_beta_cp; simpl.
        (** Now we just have to rearrange it a bit. *)
        rewrite !concat_pp_p; do 2 apply moveR_Vp; rewrite !concat_p_pp.
        apply cplr.
        Close Scope long_path_scope.
  Qed.

End CoeqInd2.
