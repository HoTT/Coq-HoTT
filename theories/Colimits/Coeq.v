From HoTT Require Import Basics.
Require Import Types.Paths Types.Arrow Types.Sigma Types.Forall Types.Universe Types.Prod.
Require Import Colimits.GraphQuotient.
Require Import Homotopy.IdentitySystems.

Local Open Scope path_scope.

(** * Homotopy coequalizers *)

(** ** Definition *)

Definition Coeq@{i j u} {B : Type@{i}} {A : Type@{j}} (f g : B -> A) : Type@{u}
  := GraphQuotient@{i j u} (fun a b => {x : B & (f x = a) * (g x = b)}).

Definition coeq {B A f g} (a : A) : @Coeq B A f g := gq a.
Definition cglue {B A f g} b : @coeq B A f g (f b) = coeq (g b)
  := gqglue (b; (idpath,idpath)).

Arguments Coeq : simpl never.
Arguments coeq : simpl never.
Arguments cglue : simpl never.

Definition Coeq_ind {B A f g} (P : @Coeq B A f g -> Type)
  (coeq' : forall a, P (coeq a))
  (cglue' : forall b, (cglue b) # (coeq' (f b)) = coeq' (g b))
  : forall w, P w.
Proof.
  rapply GraphQuotient_ind.
  intros a b [x [[] []]].
  exact (cglue' x).
Defined.

Lemma Coeq_ind_beta_cglue {B A f g} (P : @Coeq B A f g -> Type)
  (coeq' : forall a, P (coeq a))
  (cglue' : forall b, (cglue b) # (coeq' (f b)) = coeq' (g b)) (b:B)
  : apD (Coeq_ind P coeq' cglue') (cglue b) = cglue' b.
Proof.
  rapply GraphQuotient_ind_beta_gqglue.
Defined.

Definition Coeq_rec {B A f g} (P : Type) (coeq' : A -> P)
  (cglue' : forall b, coeq' (f b) = coeq' (g b))
  : @Coeq B A f g -> P.
Proof.
  rapply GraphQuotient_rec.
  intros a b [x [[] []]].
  exact (cglue' x).
Defined.

Definition Coeq_rec_beta_cglue {B A f g} (P : Type) (coeq' : A -> P)
  (cglue' : forall b:B, coeq' (f b) = coeq' (g b)) (b:B)
  : ap (Coeq_rec P coeq' cglue') (cglue b) = cglue' b.
Proof.
  rapply GraphQuotient_rec_beta_gqglue.
Defined.

Definition Coeq_ind_hprop {B A f g} (P : @Coeq B A f g -> Type)
  `{forall x, IsHProp (P x)}
  (i : forall a, P (coeq a))
  : forall x, P x.
Proof.
  snapply Coeq_ind.
  1: exact i.
  intros b.
  rapply path_ishprop.
Defined.

Definition Coeq_ind_eta_homotopic {B A f g} {P : @Coeq B A f g -> Type}
  (h : forall w : Coeq f g, P w)
  : h == Coeq_ind P (h o coeq) (fun b => apD h (cglue b)).
Proof.
  unfold pointwise_paths.
  napply (Coeq_ind _ (fun _ => 1)).
  intros b.
  lhs napply transport_paths_FlFr_D.
  lhs napply (whiskerL _ (Coeq_ind_beta_cglue _ _ _ _)).
  lhs napply (whiskerR (concat_p1 _)).
  napply concat_Vp.
Defined.

Definition Coeq_rec_eta_homotopic {B A f g} {P : Type} (h : @Coeq B A f g -> P)
  : h == Coeq_rec P (h o coeq) (fun b => ap h (cglue b)).
Proof.
  unfold pointwise_paths.
  napply (Coeq_ind _ (fun _ => 1)).
  intros b.
  transport_paths FlFr.
  apply equiv_p1_1q.
  symmetry; napply Coeq_rec_beta_cglue.
Defined.

Definition Coeq_ind_eta `{Funext}
  {B A f g} {P : @Coeq B A f g -> Type} (h : forall w : Coeq f g, P w)
  : h = Coeq_ind P (h o coeq) (fun b => apD h (cglue b))
  := path_forall _ _ (Coeq_ind_eta_homotopic h).

Definition Coeq_rec_eta `{Funext}
  {B A f g} {P : Type} (h : @Coeq B A f g -> P)
  : h = Coeq_rec P (h o coeq) (fun b => ap h (cglue b))
  := path_forall _ _ (Coeq_rec_eta_homotopic h).

Definition Coeq_ind_homotopy {B A f g} (P : @Coeq B A f g -> Type)
  {m n : forall a, P (coeq a)} (u : m == n)
  {r : forall b, (cglue b) # (m (f b)) = m (g b)}
  {s : forall b, (cglue b) # (n (f b)) = n (g b)}
  (p : forall b, ap (transport P (cglue b)) (u (f b)) @ (s b) = r b @ u (g b))
  : Coeq_ind P m r == Coeq_ind P n s.
Proof.
  unfold pointwise_paths.
  napply Coeq_ind; intros b.
  lhs napply (transport_paths_FlFr_D (f:=Coeq_ind P m r) (g:=Coeq_ind P n s)).
  lhs napply (whiskerL _ (Coeq_ind_beta_cglue P n s b)).
  lhs napply (whiskerR (whiskerR (ap inverse (Coeq_ind_beta_cglue P m r b)) _)).
  lhs napply concat_pp_p; napply moveR_Mp.
  rhs napply (whiskerR (inv_V _)).
  exact (p b).
Defined.

(** ** Universal property *)
(** See Colimits/CoeqUnivProp.v for a similar universal property without [Funext]. *)

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
    transport_paths FlFr.
    apply equiv_p1_1q.
    napply Coeq_rec_beta_cglue.
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

Definition functor_coeq_idmap {B A f g}
  : functor_coeq (B:=B) (A:=A) (f:=f) (g:=g) idmap idmap (fun _ => 1) (fun _  => 1)
    == idmap.
Proof.
  snapply Coeq_ind.
  1: reflexivity.
  intros b.
  transport_paths Flr.
  apply moveR_pM.
  napply functor_coeq_beta_cglue.
Defined.

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
  transport_paths FlFr.
  apply equiv_p1_1q; symmetry.
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
  transport_paths FlFr.
  rewrite !functor_coeq_beta_cglue.
  Open Scope long_path_scope.
  rewrite 2 ap_V.
  rewrite !concat_p_pp.
  apply moveL_pV.
  rewrite <- (ap_pp (@coeq _ _ f' g') (s (f b)) (p' b)).
  rewrite u, ap_pp.
  rewrite !concat_pp_p; apply whiskerL.
  rewrite <- (ap_pp (@coeq _ _ f' g') (s (g b)) (q' b)).
  rewrite v, ap_pp.
  rewrite concat_V_pp.
  rewrite <- 2 ap_compose.
  exact (concat_Ap (@cglue _ _ f' g') (r b))^.
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

  #[export] Instance isequiv_functor_coeq
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
  Context {B A : Type} {f g : B -> A} {B' A' : Type} {f' g' : B' -> A'}
    (P : Type) (coeq' : A -> A' -> P)
    (cgluel : forall b a', coeq' (f b) a' = coeq' (g b) a')
    (cgluer : forall a b', coeq' a (f' b') = coeq' a (g' b'))
    (cgluelr : forall b b', cgluel b (f' b') @ cgluer (g b) b'
                          = cgluer (f b) b' @ cgluel b (g' b')).

  Definition Coeq_rec2 : Coeq f g -> Coeq f' g' -> P.
  Proof.
    intros x y; revert x.
    snapply Coeq_rec.
    - intros a.
      revert y.
      snapply Coeq_rec.
      + intros a'.
        exact (coeq' a a').
      + intros b'; cbn.
        apply cgluer.
    - intros b.
      revert y.
      snapply Coeq_ind.
      + intros a'.
        cbn.
        apply cgluel.
      + intros b'.
        transport_paths (transport_paths_FlFr (cglue b')).
        lhs napply (_ @@ 1).
        1: apply Coeq_rec_beta_cglue.
        rhs napply (1 @@ _).
        2: apply Coeq_rec_beta_cglue.
        symmetry.
        apply cgluelr.
  Defined.

  Definition Coeq_rec2_beta (a : A) (a' : A')
    : Coeq_rec2 (coeq a) (coeq a') = coeq' a a'
    := 1.

  Definition Coeq_rec2_beta_cgluel (a : A) (b' : B')
    : ap (Coeq_rec2 (coeq a)) (cglue b') = cgluer a b'.
  Proof.
    napply Coeq_rec_beta_cglue.
  Defined.

  Definition Coeq_rec2_beta_cgluer (b : B) (a' : A')
    : ap (fun x => Coeq_rec2 x (coeq a')) (cglue b) = cgluel b a'.
  Proof.
    napply Coeq_rec_beta_cglue.
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

(** ** Descent *)

(** We study "equifibrant" type families over a parallel pair [f, g: B -> A].  By univalence, the descent property tells us that these type families correspond to type families over the coequalizer, and we obtain an induction principle for such type families.  Dependent descent data over some particular descent data are "equifibrant" type families over this descent data.  The "equifibrancy" is only taken over the parallel pair [f g : B -> A], but there is an extra level of dependency coming from the descent data.  In this case, we obtain an induction and recursion principle, but only with a computation rule for the recursion principle.

The theory of descent is interesting to consider in itself.  However, we will use it as a means to structure the code, and to obtain induction and recursion principles that are valuable in proving the flattening lemma, and characterizing path spaces.  Thus we will gloss over the bigger picture, and not consider equivalences of descent data, nor homotopies of their sections.  We will also not elaborate on uniqueness of the induced families.

It's possible to prove the results in the Descent, Flattening and Paths Sections without univalence, by replacing all equivalences with paths, but in practice these results will be used with equivalences as input, making the form below more convenient.  See https://github.com/HoTT/Coq-HoTT/pull/2147#issuecomment-2521570830 for further information *)

Section Descent.

  Context `{Univalence}.

  (** Descent data over [f g : B -> A] is an "equifibrant" or "cartesian" type family [cd_fam : A -> Type].  This means that if [b : B], then the fibers [cd_fam (f b)] and [cd_fam (g b)] are equivalent, witnessed by [cd_e]. *)
  Record cDescent {A B : Type} {f g : B -> A} := {
    cd_fam (a : A) : Type;
    cd_e (b : B) : cd_fam (f b) <~> cd_fam (g b)
  }.
  Global Arguments cDescent {A B} f g.

  (** Let [A] and [B] be types, with a parallel pair [f g : B -> A]. *)
  Context {A B : Type} {f g : B -> A}.

  (** Descent data induces a type family over [Coeq f g]. *)
  Definition fam_cdescent (Pe : cDescent f g)
    : Coeq f g -> Type.
  Proof.
    snapply (Coeq_rec _ (cd_fam Pe)).
    intro b.
    exact (path_universe_uncurried (cd_e Pe b)).
  Defined.

  (** A type family over [Coeq f g] induces descent data. *)
  Definition cdescent_fam (P : Coeq f g -> Type) : cDescent f g.
  Proof.
    snapply Build_cDescent.
    - exact (P o coeq).
    - intro b.
      exact (equiv_transport P (cglue b)).
  Defined.

  (** Transporting over [fam_cdescent] along [cglue b] is given by [cd_e]. *)
  Definition transport_fam_cdescent_cglue
    (Pe : cDescent f g) (b : B) (pf : cd_fam Pe (f b))
    : transport (fam_cdescent Pe) (cglue b) pf = cd_e Pe b pf.
  Proof.
    napply transport_path_universe'.
    napply Coeq_rec_beta_cglue.
  Defined.

  (** A section on the descent data is a fiberwise section that respects the equivalences. *)
  Record cDescentSection {Pe : cDescent f g} := {
    cds_sect (a : A) : cd_fam Pe a;
    cds_e (b : B) : cd_e Pe b (cds_sect (f b)) = cds_sect (g b)
  }.

  Global Arguments cDescentSection Pe : clear implicits.

  (** A descent section induces a genuine section of [fam_cdescent Pe]. *)
  Definition cdescent_ind {Pe : cDescent f g}
    (s : cDescentSection Pe)
    : forall (x : Coeq f g), fam_cdescent Pe x.
  Proof.
    snapply (Coeq_ind _ (cds_sect s)).
    intro b.
    exact (transport_fam_cdescent_cglue Pe b _ @ cds_e s b).
  Defined.

  (** We record its computation rule *)
  Definition cdescent_ind_beta_cglue {Pe : cDescent f g}
    (s : cDescentSection Pe) (b : B)
    : apD (cdescent_ind s) (cglue b) = transport_fam_cdescent_cglue Pe b _ @ cds_e s b
    := Coeq_ind_beta_cglue _ (cds_sect s) _ _.

  (** Dependent descent data over descent data [Pe : cDescent f g] consists of a type family [cdd_fam : forall a : A, cd_fam Pe a -> Type] together with coherences [cdd_e b pf]. *)
  Record cDepDescent {Pe : cDescent f g} := {
    cdd_fam (a : A) (pa : cd_fam Pe a) : Type;
    cdd_e (b : B) (pf : cd_fam Pe (f b))
      : cdd_fam (f b) pf <~> cdd_fam (g b) (cd_e Pe b pf)
  }.

  Global Arguments cDepDescent Pe : clear implicits.

  (** A dependent type family over [fam_cdescent Pe] induces dependent descent data over [Pe]. *)
  Definition cdepdescent_fam {Pe : cDescent f g}
    (Q : forall x : Coeq f g, (fam_cdescent Pe) x -> Type)
    : cDepDescent Pe.
  Proof.
    snapply Build_cDepDescent.
    - intro a; cbn.
      exact (Q (coeq a)).
    - intros b pf.
      exact (equiv_transportDD (fam_cdescent Pe) Q
               (cglue b) (transport_fam_cdescent_cglue Pe b pf)).
  Defined.

  (** Dependent descent data over [Pe] induces a dependent type family over [fam_cdescent Pe]. *)
  Definition fam_cdepdescent {Pe : cDescent f g} (Qe : cDepDescent Pe)
    : forall (x : Coeq f g), (fam_cdescent Pe x) -> Type.
  Proof.
    snapply Coeq_ind.
    - exact (cdd_fam Qe).
    - intro b.
      napply (moveR_transport_p _ (cglue b)).
      funext pa.
      rhs napply transport_arrow_toconst.
      rhs nrefine (ap (cdd_fam _ _) _).
      + exact (path_universe (cdd_e _ _ _)).
      + lhs napply (ap (fun x => (transport _ x _)) (inv_V (cglue _))).
        exact (transport_fam_cdescent_cglue _ _ _).
  Defined.

  (** A section of dependent descent data [Qe : cDepDescent Pe] is a fiberwise section [cdds_sect], together with coherences [cdds_e]. *)
  Record cDepDescentSection {Pe : cDescent f g} {Qe : cDepDescent Pe} := {
    cdds_sect (a : A) (pa : cd_fam Pe a) : cdd_fam Qe a pa;
    cdds_e (b : B) (pf : cd_fam Pe (f b))
      : cdd_e Qe b pf (cdds_sect (f b) pf) = cdds_sect (g b) (cd_e Pe b pf)
  }.

  Global Arguments cDepDescentSection {Pe} Qe.

  (** A dependent descent section induces a genuine section over the total space of [fam_cdescent Pe]. *)
  Definition cdepdescent_ind {Pe : cDescent f g}
    {Q : forall (x : Coeq f g), (fam_cdescent Pe) x -> Type}
    (s : cDepDescentSection (cdepdescent_fam Q))
    : forall (x : Coeq f g) (px : fam_cdescent Pe x), Q x px.
    Proof.
      napply (Coeq_ind _ (cdds_sect s) _).
      intro b.
      apply dpath_forall.
      intro pf.
      apply (equiv_inj (transport (Q (coeq (g b))) (transport_fam_cdescent_cglue Pe b pf))).
      rhs exact (apD (cdds_sect s (g b)) (transport_fam_cdescent_cglue Pe b pf)).
      exact (cdds_e s b pf).
    Defined.

  (** The data for a section into a constant type family. *)
  Record cDepDescentConstSection {Pe : cDescent f g} {Q : Type} := {
    cddcs_sect (a : A) (pa : cd_fam Pe a) : Q;
    cddcs_e (b : B) (pf : cd_fam Pe (f b))
      : cddcs_sect (f b) pf = cddcs_sect (g b) (cd_e Pe b pf)
  }.

  Global Arguments cDepDescentConstSection Pe Q : clear implicits.

  (** The data for a section of a constant family induces a section over the total space of [fam_cdescent Pe]. *)
  Definition cdepdescent_rec {Pe : cDescent f g} {Q : Type}
    (s : cDepDescentConstSection Pe Q)
    : forall (x : Coeq f g), fam_cdescent Pe x -> Q.
  Proof.
    snapply (Coeq_ind _ (cddcs_sect s)).
    intro b.
    napply dpath_arrow.
    intro pf.
    lhs napply transport_const.
    rhs napply (ap _ (transport_fam_cdescent_cglue Pe b pf)).
    exact (cddcs_e s b pf).
  Defined.

  (** Here is the computation rule on paths. *)
  Definition cdepdescent_rec_beta_cglue {Pe : cDescent f g} {Q : Type}
    (s : cDepDescentConstSection Pe Q)
    (b : B) {pf : cd_fam Pe (f b)} {pg : cd_fam Pe (g b)} (pb : cd_e Pe b pf = pg)
    : ap (sig_rec (cdepdescent_rec s)) (path_sigma _ (coeq (f b); pf) (coeq (g b); pg) (cglue b) (transport_fam_cdescent_cglue Pe b pf @ pb))
      = cddcs_e s b pf @ ap (cddcs_sect s (g b)) pb.
  Proof.
    Open Scope long_path_scope.
    destruct pb.
    rhs napply concat_p1.
    lhs napply ap_sig_rec_path_sigma.
    lhs napply (ap (fun x => _ (ap10 x _) @ _)).
    1: napply Coeq_ind_beta_cglue.
    do 3 lhs napply concat_pp_p.
    apply moveR_Vp.
    lhs nrefine (1 @@ (1 @@ (_ @@ 1))).
    1: napply (ap10_dpath_arrow (fam_cdescent Pe) (fun _ => Q) (cglue b)).
    lhs nrefine (1 @@ _).
    { lhs napply (1 @@ concat_pp_p _ _ _).
      lhs napply (1 @@ concat_pp_p _ _ _).
      lhs napply concat_V_pp.
      lhs napply (1 @@ concat_pp_p _ _ _).
      rewrite concat_p1.
      exact (1 @@ (1 @@ concat_pV_p _ _)). }
    napply concat_V_pp.
    Close Scope long_path_scope.
  Defined.

End Descent.

(** ** The flattening lemma *)

(** We saw above that given descent data [Pe] over a parallel pair [f g : B -> A], we obtained a type family [fam_cdescent Pe] over the coequalizer.  The flattening lemma describes the total space [sig (fam_cdescent Pe)] of this type family as a coequalizer of [sig (cd_fam Pe)] by a certain parallel pair.  This follows from the work above, which shows that [sig (fam_cdescent Pe)] has the same universal property as this coequalizer.

The flattening lemma here also follows from the flattening lemma for [GraphQuotients], avoiding the need for the material in Section Descent.  However, that material is likely useful in general, so we have given an independent proof of the flattening lemma.  See versions of the library before December 5, 2024 for the proof using the flattening lemma for [GraphQuotients]. *)

Section Flattening.

  Context `{Univalence} {A B : Type} {f g : B -> A} (Pe : cDescent f g).

  (** We mimic the constructors of [Coeq] for the total space.  Here is the point constructor, in curried form. *)
  Definition flatten_cd {a : A} (pa : cd_fam Pe a) : sig (fam_cdescent Pe)
    := (coeq a; pa).

  (** And here is the path constructor. *)
  Definition flatten_cd_glue (b : B)
    {pf : cd_fam Pe (f b)} {pg : cd_fam Pe (g b)} (pb : cd_e Pe b pf = pg)
    : flatten_cd pf = flatten_cd pg.
  Proof.
    snapply path_sigma.
    - by apply cglue.
    - lhs napply transport_fam_cdescent_cglue.
      exact pb.
  Defined.

  (** Now that we've shown that [fam_cdescent Pe] acts like a [Coeq] of [sig (cd_fam Pe)] by an appropriate parallel pair, we can use this to prove the flattening lemma.  The maps back and forth are very easy so this could almost be a formal consequence of the induction principle. *)
  Lemma equiv_cd_flatten : sig (fam_cdescent Pe) <~>
    Coeq (functor_sigma f (fun _ => idmap)) (functor_sigma g (cd_e Pe)).
  Proof.
    snapply equiv_adjointify.
    - snapply sig_rec.
      snapply cdepdescent_rec.
      snapply Build_cDepDescentConstSection.
      + exact (fun a x => coeq (a; x)).
      + intros b pf.
      cbn.
      exact (@cglue _ _
        (functor_sigma f (fun _ => idmap)) (functor_sigma g (cd_e Pe)) (b; pf)).
    - snapply Coeq_rec.
      + exact (fun '(a; x) => (coeq a; x)).
      + intros [b pf]; cbn.
        exact (flatten_cd_glue b 1).
    - snapply Coeq_ind; cbn beta.
      1: reflexivity.
      intros [b pf]; cbn.
      transport_paths FFlr; apply equiv_p1_1q.
      rewrite Coeq_rec_beta_cglue.
      lhs napply cdepdescent_rec_beta_cglue.
      napply concat_p1.
    - intros [x px]; revert x px.
      snapply cdepdescent_ind.
      snapply Build_cDepDescentSection.
      + by intros a pa.
      + intros b pf; cbn.
        lhs napply transportDD_is_transport.
        transport_paths FFlr; apply equiv_p1_1q.
        rewrite <- (concat_p1 (transport_fam_cdescent_cglue _ _ _)).
        rewrite cdepdescent_rec_beta_cglue. (* This needs to be in the form [transport_fam_cdescent_cglue Pe r pa @ p] to work, and the other [@ 1] introduced comes in handy as well. *)
        lhs napply (ap _ (concat_p1 _)).
        exact (Coeq_rec_beta_cglue _ _ _ (b; pf)).
  Defined.

End Flattening.

(** ** Characterization of path spaces *)

(** A pointed type family over a coequalizer has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022. *)

Section Paths.

  (** Let [f g : B -> A] be a parallel pair, with a distinguished point [a0 : A].  Let [Pe : cDescent f g] be descent data over [f g] with a distinguished point [p0 : cd_fam Pe a0].  Assume that any dependent descent data [Qe : cDepDescent Pe] with a distinguished point [q0 : cdd_fam Qe a0 p0] has a section that respects the distinguished points.  This is the induction principle provided by Kraus and von Raumer. *)
  Context `{Univalence} {A B: Type} {f g : B -> A} (a0 : A)
    (Pe : cDescent f g) (p0 : cd_fam Pe a0)
    (based_cdepdescent_ind : forall (Qe : cDepDescent Pe) (q0 : cdd_fam Qe a0 p0),
      cDepDescentSection Qe)
    (based_cdepdescent_ind_beta : forall (Qe : cDepDescent Pe) (q0 : cdd_fam Qe a0 p0),
      cdds_sect (based_cdepdescent_ind Qe q0) a0 p0 = q0).

  (** Under these hypotheses, we get an identity system structure on [fam_cdescent Pe]. *)
  Local Instance idsys_flatten_cdescent
    : @IsIdentitySystem _ (coeq a0) (fam_cdescent Pe) p0.
  Proof.
    snapply Build_IsIdentitySystem.
    - intros Q q0 x p.
      snapply cdepdescent_ind.
      by apply based_cdepdescent_ind.
    - intros Q q0; cbn.
      napply (based_cdepdescent_ind_beta (cdepdescent_fam Q)).
  Defined.

  (** It follows that the fibers [fam_cdescent Pe x] are equivalent to path spaces [(coeq a0) = x]. *)
  Definition induced_fam_cd_equiv_path (x : Coeq f g)
    : (coeq a0) = x <~> fam_cdescent Pe x
    := @equiv_transport_identitysystem _ (coeq a0) (fam_cdescent Pe) p0 _ x.

End Paths.
