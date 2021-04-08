(* -*- mode: coq; mode: visual-line -*- *)

(** * Homotopy coequalizers *)

Require Import HoTT.Basics.
Require Import HoTT.Types.Paths HoTT.Types.Forall HoTT.Types.Sigma HoTT.Types.Arrow HoTT.Types.Universe.
Require Import HoTT.Cubical.DPath.
Local Open Scope path_scope.

(** ** Definition *)

Module Export Coeq.

  Private Inductive Coeq {B : Type@{i}} {A : Type@{j}}
    (f g : B -> A) : Type@{max(i,j)} :=
      | coeq : A -> Coeq f g.

  Arguments coeq {B A f g} a.

  Axiom cglue : forall {B A f g} (b:B), @coeq B A f g (f b) = coeq (g b).

  Definition Coeq_ind {B A f g} (P : @Coeq B A f g -> Type)
             (coeq' : forall a, P (coeq a))
             (cglue' : forall b, (cglue b) # (coeq' (f b)) = coeq' (g b))
  : forall w, P w
    := fun w => match w with coeq a => fun _ => coeq' a end cglue'.

  Axiom Coeq_ind_beta_cglue
  : forall {B A f g} (P : @Coeq B A f g -> Type)
           (coeq' : forall a, P (coeq a))
           (cglue' : forall b, (cglue b) # (coeq' (f b)) = coeq' (g b)) (b:B),
      apD (Coeq_ind P coeq' cglue') (cglue b) = cglue' b.

End Coeq.

Definition Coeq_rec {B A f g} (P : Type) (coeq' : A -> P)
  (cglue' : forall b, coeq' (f b) = coeq' (g b))
  : @Coeq B A f g -> P
  := Coeq_ind (fun _ => P) coeq' (fun b => transport_const _ _ @ cglue' b).

Definition Coeq_rec_beta_cglue {B A f g} (P : Type) (coeq' : A -> P)
  (cglue' : forall b:B, coeq' (f b) = coeq' (g b)) (b:B)
  : ap (Coeq_rec P coeq' cglue') (cglue b) = cglue' b.
Proof.
  unfold Coeq_rec.
  (** Use [eapply] rather than [refine] so that we don't get evars as goals, and don't have to shelve any goals with [shelve_unifiable]. *)
  eapply (cancelL (transport_const (cglue b) _)).
  refine ((apD_const (@Coeq_ind B A f g (fun _ => P) coeq' _) (cglue b))^ @ _).
  refine (Coeq_ind_beta_cglue (fun _ => P) _ _ _).
Defined.

Definition Coeq_ind_dp {B A f g} (P : @Coeq B A f g -> Type)
             (coeq' : forall a, P (coeq a))
             (cglue' : forall b, DPath P (cglue b) (coeq' (f b)) (coeq' (g b)))
  : forall w, P w.
Proof.
  srapply (Coeq_ind P coeq'); intros b.
  apply dp_path_transport^-1, cglue'.
Defined.

Definition Coeq_ind_dp_beta_cglue {B A f g} (P : @Coeq B A f g -> Type)
             (coeq' : forall a, P (coeq a))
             (cglue' : forall b, DPath P (cglue b) (coeq' (f b)) (coeq' (g b)))
             (b : B)
  : dp_apD (Coeq_ind_dp P coeq' cglue') (cglue b) = cglue' b.
Proof.
  apply dp_apD_path_transport.
  srapply Coeq_ind_beta_cglue.
Defined.

(** ** Universal property *)

Definition Coeq_unrec {B A} (f g : B -> A) {P}
           (h : Coeq f g -> P)
  : {k : A -> P & k o f == k o g}.
Proof.
  exists (h o coeq).
  intros b. exact (ap h (cglue b)).
Defined.

Definition isequiv_Coeq_rec `{Funext} {B A} (f g : B -> A) P
  : IsEquiv (fun p : {h : A -> P & h o f == h o g} => Coeq_rec P p.1 p.2).
Proof.
  srapply (isequiv_adjointify _ (Coeq_unrec f g)).
  - intros h.
    apply path_arrow.
    srapply Coeq_ind; intros b.
    1: cbn;reflexivity.
    cbn.
    abstract (rewrite transport_paths_FlFr, concat_p1, Coeq_rec_beta_cglue, concat_Vp; reflexivity).
  - intros [h q]; srapply path_sigma'.
    + reflexivity.
    + cbn.
      rapply path_forall; intros b.
      apply Coeq_rec_beta_cglue.
Defined.

Definition equiv_Coeq_rec `{Funext} {B A} (f g : B -> A) P
  : {h : A -> P & h o f == h o g} <~> (Coeq f g -> P)
  := Build_Equiv _ _ _ (isequiv_Coeq_rec f g P).

(** ** Functoriality *)

Definition functor_coeq {B A f g B' A' f' g'}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
: @Coeq B A f g -> @Coeq B' A' f' g'.
Proof.
  refine (Coeq_rec _ (coeq o k) _); intros b.
  refine (ap coeq (p b) @ _ @ ap coeq (q b)^).
  apply cglue.
Defined.

Definition functor_coeq_beta_cglue {B A f g B' A' f' g'}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
           (b : B)
: ap (functor_coeq h k p q) (cglue b)
  = ap coeq (p b) @ cglue (h b) @ ap coeq (q b)^
:= (Coeq_rec_beta_cglue _ _ _ b).

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
  rewrite !functor_coeq_beta_cglue, !ap_pp, functor_coeq_beta_cglue.
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
  refine (transport_paths_FlFr (cglue b) _ @ _).
  rewrite concat_pp_p; apply moveR_Vp.
  rewrite !functor_coeq_beta_cglue.
  Open Scope long_path_scope.
  rewrite !concat_p_pp.
  rewrite <- (ap_pp (@coeq _ _ f' g') (s (f b)) (p' b)).
  rewrite u, ap_pp, !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
  rewrite ap_V; apply moveR_pV.
  rewrite !concat_pp_p, <- (ap_pp (@coeq _ _ f' g') (s (g b)) (q' b)).
  rewrite v, ap_pp, ap_V, concat_V_pp.
  rewrite <- !ap_compose.
  exact (concat_Ap (@cglue _ _ f' g') (r b)).
  Close Scope long_path_scope.
Qed.

Definition functor_coeq_sect {B A f g B' A' f' g'}
           (h : B -> B') (k : A -> A')
           (p : k o f == f' o h) (q : k o g == g' o h)
           (h' : B' -> B) (k' : A' -> A)
           (p' : k' o f' == f o h') (q' : k' o g' == g o h')
           (r : h' o h == idmap) (s : k' o k == idmap)
           (u : forall b, ap k' (p b) @ p' (h b) @ ap f (r b) = s (f b))
           (v : forall b, ap k' (q b) @ q' (h b) @ ap g (r b) = s (g b))
: (functor_coeq h' k' p' q') o (functor_coeq h k p q) == idmap.
Proof.
  refine (Coeq_ind _ (fun a => ap coeq (s a)) _); cbn; intros b.
  refine (transport_paths_FFlr (cglue b) _ @ _).
  rewrite concat_pp_p; apply moveR_Vp.
  rewrite functor_coeq_beta_cglue, !ap_pp.
  rewrite <- !ap_compose; cbn.
  rewrite functor_coeq_beta_cglue.
  Open Scope long_path_scope.
  rewrite !concat_p_pp.
  rewrite <- u, !ap_pp, !(ap_compose k' coeq).
  rewrite !concat_pp_p; do 2 apply whiskerL.
  rewrite !concat_p_pp.
  rewrite <- v.
  rewrite !ap_pp, !ap_V, !concat_p_pp, !concat_pV_p.
  rewrite <- !ap_compose.
  exact (concat_Ap cglue (r b)).
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
  : (functor_coeq h k p q) o functor_coeq_inverse == idmap.
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
  : functor_coeq_inverse o (functor_coeq h k p q) == idmap.
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
    := Build_Equiv _ _ (functor_coeq h k p q) _.

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
          (cgluel : forall b a', coeq' (f b) a' = coeq' (g b) a')
          (cgluer : forall a b', coeq' a (f' b') = coeq' a (g' b'))
          (cgluelr : forall b b', cgluel b (f' b') @ cgluer (g b) b'
                               = cgluer (f b) b' @ cgluel b (g' b')).

  Definition Coeq_rec2
  : Coeq f g -> Coeq f' g' -> P.
  Proof.
    simple refine (Coeq_rec _ _ _).
    - intros a.
      simple refine (Coeq_rec _ _ _).
      + intros a'.
        exact (coeq' a a').
      + intros b'; cbn.
        apply cgluer.
    - intros b.
      apply path_arrow; intros a.
      revert a; simple refine (Coeq_ind _ _ _).
      + intros a'. cbn.
        apply cgluel.
      + intros b'; cbn.
        refine (transport_paths_FlFr (cglue b') (cgluel b (f' b')) @ _).
        refine (concat_pp_p _ _ _ @ _).
        apply moveR_Vp.
        refine (_ @ cgluelr b b' @ _).
        * apply whiskerL.
          apply Coeq_rec_beta_cglue.
        * apply whiskerR.
          symmetry; apply Coeq_rec_beta_cglue.
  Defined.

  Definition Coeq_rec2_beta (a : A) (a' : A')
  : Coeq_rec2 (coeq a) (coeq a') = coeq' a a'
    := 1.

  Definition Coeq_rec2_beta_cgluel (a : A) (b' : B')
  : ap (Coeq_rec2 (coeq a)) (cglue b') = cgluer a b'.
  Proof.
    apply Coeq_rec_beta_cglue.
  Defined.

  Definition Coeq_rec2_beta_cgluer (b : B) (a' : A')
  : ap (fun x => Coeq_rec2 x (coeq a')) (cglue b) = cgluel b a'.
  Proof.
    transitivity (ap10 (ap Coeq_rec2 (cglue b)) (coeq a')).
    - refine (ap_compose Coeq_rec2 (fun h => h (coeq a')) _ @ _).
      apply ap_apply_l.
    - unfold Coeq_rec2; rewrite Coeq_rec_beta_cglue.
      rewrite ap10_path_arrow.
      reflexivity.
  Defined.

  (** TODO: [Coeq_rec2_beta_cgluelr] *)

End CoeqRec2.

(** ** A double induction principle *)

Section CoeqInd2.
  Context `{Funext}
          {B A : Type} {f g : B -> A} {B' A' : Type} {f' g' : B' -> A'}
          (P : Coeq f g -> Coeq f' g' -> Type)
          (coeq' : forall a a', P (coeq a) (coeq a'))
          (cgluel : forall b a',
                   transport (fun x => P x (coeq a')) (cglue b)
                             (coeq' (f b) a') = coeq' (g b) a')
          (cgluer : forall a b',
                   transport (fun y => P (coeq a) y) (cglue b')
                             (coeq' a (f' b')) = coeq' a (g' b'))
          (** Perhaps this should really be written using [concatD]. *)
          (cgluelr : forall b b',
                  ap (transport (P (coeq (g b))) (cglue b')) (cgluel b (f' b'))
                  @ cgluer (g b) b'
                  = transport_transport P (cglue b) (cglue b') (coeq' (f b) (f' b'))
                  @ ap (transport (fun x => P x (coeq (g' b'))) (cglue b))
                       (cgluer (f b) b')
                  @ cgluel b (g' b')).

  Definition Coeq_ind2
  : forall x y, P x y.
  Proof.
    simple refine (Coeq_ind _ _ _).
    - intros a.
      simple refine (Coeq_ind _ _ _).
      + intros a'.
        exact (coeq' a a').
      + intros b'; cbn.
        apply cgluer.
    - intros b.
      apply path_forall; intros a.
      revert a; simple refine (Coeq_ind _ _ _).
      + intros a'. cbn.
        refine (transport_forall_constant _ _ _ @ _).
        apply cgluel.
      + intros b'; cbn.
        refine (transport_paths_FlFr_D (cglue b') _ @ _).
        rewrite Coeq_ind_beta_cglue.
        (** Now begins the long haul. *)
        Open Scope long_path_scope.
        rewrite ap_pp.
        repeat rewrite concat_p_pp.
        (** Our first order of business is to get rid of the [Coeq_ind]s, which only occur in the following incarnation. *)
        set (G := (Coeq_ind (P (coeq (f b)))
                            (fun a' : A' => coeq' (f b) a')
                            (fun b'0 : B' => cgluer (f b) b'0))).
        (** Let's reduce the [apD (loop # G)] first. *)
        rewrite (apD_transport_forall_constant P (cglue b) G (cglue b')); simpl.
        rewrite !inv_pp, !inv_V.
        (** Now we can cancel a [transport_forall_constant]. *)
        rewrite !concat_pp_p; apply whiskerL.
        (** And a path-inverse pair.  This removes all the [transport_forall_constant]s. *)
        rewrite !concat_p_pp, concat_pV_p.
        (** Now we can beta-reduce the last remaining [G]. *)
        subst G; rewrite Coeq_ind_beta_cglue; simpl.
        (** Now we just have to rearrange it a bit. *)
        rewrite !concat_pp_p; do 2 apply moveR_Vp; rewrite !concat_p_pp.
        apply cgluelr.
        Close Scope long_path_scope.
  Qed.

End CoeqInd2.

(** ** Symmetry *)

Definition Coeq_sym_map {B A} (f g : B -> A) : Coeq f g -> Coeq g f :=
  Coeq_rec (Coeq g f) coeq (fun b : B => (cglue b)^).

Lemma sect_Coeq_sym_map {B A} {f g : B -> A}
  : (Coeq_sym_map f g) o (Coeq_sym_map g f) == idmap.
Proof.
  srapply @Coeq_ind.
  - reflexivity.
  - intro b.
    simpl.
    abstract (rewrite transport_paths_FFlr, Coeq_rec_beta_cglue, ap_V, Coeq_rec_beta_cglue; hott_simpl).
Defined.

Lemma Coeq_sym {B A} {f g : B -> A} : @Coeq B A f g <~> Coeq g f.
Proof.
  exact (equiv_adjointify (Coeq_sym_map f g) (Coeq_sym_map g f) sect_Coeq_sym_map sect_Coeq_sym_map).
Defined.
