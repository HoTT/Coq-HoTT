From HoTT Require Import Basics Types.
Require Import Pointed WildCat.
Require Import Cubical.DPath Cubical.PathSquare Cubical.DPathSquare.
Require Import Algebra.AbGroups.
Require Import Homotopy.HSpace.Core.
Require Import TruncType.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.WhiteheadsPrinciple.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * Classifying spaces of groups *)

(** We define the classifying space of a group to be the following HIT:

<<
  HIT ClassifyingSpace (G : Group) : 1-Type
   | bbase : ClassifyingSpace
   | bloop : X -> bbase = bbase
   | bloop_pp : forall x y, bloop (x * y) = bloop x @ bloop y.
>>

  We implement this is a private inductive type. *)
Module Export ClassifyingSpace.

  Section ClassifyingSpace.

    Private Inductive ClassifyingSpace (G : Group) :=
      | bbase : ClassifyingSpace G.

    Context {G : Group}.

    Axiom bloop : G -> bbase G = bbase G.

    Global Arguments bbase {_}.

    Axiom bloop_pp : forall x y, bloop (x * y) = bloop x @ bloop y.

    #[export] Instance istrunc_ClassifyingSpace
      : IsTrunc 1 (ClassifyingSpace G).
    Proof. Admitted.

  End ClassifyingSpace.
  
  Arguments bloop {G} _%_mc_mult_scope.

  (** Now we can state the expected dependent elimination principle, and derive other versions of the elimination principle from it. *)
  Section ClassifyingSpace_ind.

    Local Open Scope dpath_scope.

    Context {G : Group}.

    (** Note that since our classifying space is 1-truncated, we can only eliminate into 1-truncated type families. *)
    Definition ClassifyingSpace_ind
      (P : ClassifyingSpace G -> Type)
      `{forall b, IsTrunc 1 (P b)}
      (bbase' : P bbase)
      (bloop' : forall x, DPath P (bloop x) bbase' bbase')
      (bloop_pp' : forall x y,  DPathSquare P (sq_G1 (bloop_pp x y))
        (bloop' (x * y)) ((bloop' x) @Dp (bloop' y)) 1 1)
      (b : ClassifyingSpace G)
      : P b
      := match b with
            bbase => (fun _ _ => bbase')
         end bloop' bloop_pp'.

    (** Here we state the computation rule for [ClassifyingSpace_ind] over [bloop] as an axiom. We don't need one for [bloop_pp] since we have a 1-type. We leave this as admitted since the computation rule is an axiom. **)
    Definition ClassifyingSpace_ind_beta_bloop
      (P : ClassifyingSpace G -> Type)
     `{forall b, IsTrunc 1 (P b)}
      (bbase' : P bbase) (bloop' : forall x, DPath P (bloop x) bbase' bbase')
      (bloop_pp' : forall x y,  DPathSquare P (sq_G1 (bloop_pp x y))
        (bloop' (x * y)) ((bloop' x) @Dp (bloop' y)) 1 1)
      (x : G)
      : apD (ClassifyingSpace_ind P bbase' bloop' bloop_pp') (bloop x) = bloop' x.
    Proof. Admitted.

  End ClassifyingSpace_ind.

End ClassifyingSpace.

(** Other eliminators *)
Section Eliminators.

  Context {G : Group}.

  (** The non-dependent eliminator *)
  Definition ClassifyingSpace_rec
    (P : Type) `{IsTrunc 1 P} (bbase' : P) (bloop' : G -> bbase' = bbase')
    (bloop_pp' : forall x y : G, bloop' (x * y) = bloop' x @ bloop' y)
    : ClassifyingSpace G -> P.
  Proof.
    srefine (ClassifyingSpace_ind (fun _ => P) bbase' _ _).
    1: intro x; apply dp_const, bloop', x.
    intros x y.
    apply ds_const'.
    rapply sq_GGcc.
    2: refine (_ @ ap _ (dp_const_pp _ _)).
    1,2: symmetry; apply eissect.
    by apply sq_G1.
  Defined.

  (** Computation rule for non-dependent eliminator *)
  Definition ClassifyingSpace_rec_beta_bloop
    (P : Type) `{IsTrunc 1 P} (bbase' : P) (bloop' : G -> bbase' = bbase')
    (bloop_pp' : forall x y : G, bloop' (x * y) = bloop' x @ bloop' y) (x : G)
    : ap (ClassifyingSpace_rec P bbase' bloop' bloop_pp') (bloop x) = bloop' x.
  Proof.
    lhs_V napply dp_apD_const'.
    apply moveR_equiv_V.
    napply ClassifyingSpace_ind_beta_bloop.
  Defined.

  (** Sometimes we want to induct into a set which means we can ignore the bloop_pp arguments. Since this is a routine argument, we turn it into a special case of our induction principle. *)
  Definition ClassifyingSpace_ind_hset
    (P : ClassifyingSpace G -> Type)
    `{forall b, IsTrunc 0 (P b)}
    (bbase' : P bbase) (bloop' : forall x, DPath P (bloop x) bbase' bbase')
    : forall b, P b.
  Proof.
    refine (ClassifyingSpace_ind P bbase' bloop' _).
    intros x y.
    apply ds_G1.
    apply path_ishprop.
  Defined.

  Definition ClassifyingSpace_rec_hset
    (P : Type) `{IsTrunc 0 P} (bbase' : P) (bloop' : G -> bbase' = bbase')
    : ClassifyingSpace G -> P.
  Proof.
    srapply (ClassifyingSpace_rec P bbase' bloop' _).
    intros; apply path_ishprop.
  Defined.

  (** Similarly, when eliminating into an hprop, we only have to handle the basepoint. *)
  Definition ClassifyingSpace_ind_hprop (P : ClassifyingSpace G -> Type)
    `{forall b, IsTrunc (-1) (P b)} (bbase' : P bbase)
    : forall b, P b.
  Proof.
    refine (ClassifyingSpace_ind_hset P bbase' _).
    intros; rapply dp_ishprop.
  Defined.

End Eliminators.

(** The classifying space is 0-connected. *)
Instance isconnected_classifyingspace {G : Group}
  : IsConnected 0 (ClassifyingSpace G).
Proof.
  apply (Build_Contr _ (tr bbase)).
  srapply Trunc_ind.
  srapply ClassifyingSpace_ind_hprop; reflexivity.
Defined.

(** The classifying space of a group is pointed. *)
Instance ispointed_classifyingspace (G : Group)
  : IsPointed (ClassifyingSpace G)
  := bbase.

Definition pClassifyingSpace (G : Group) := [ClassifyingSpace G, bbase].

(** To use the [B G] notation for [pClassifyingSpace] import this module. *)
Module Import ClassifyingSpaceNotation.
  Definition B G := pClassifyingSpace G.
End ClassifyingSpaceNotation.

(** [bloop] takes the unit of the group to reflexivity. *)
Definition bloop_id {G : Group} : bloop (mon_unit : G) = idpath.
Proof.
  symmetry.
  apply (cancelL (bloop mon_unit)).
  refine (_ @ bloop_pp _ _).
  refine (_ @ ap _ (left_identity _)^).
  apply concat_p1.
Defined.

(** [bloop] "preserves inverses" by taking inverses in [G] to inverses of paths in [BG]. *)
Definition bloop_inv {G : Group} (x : G) : bloop x^ = (bloop x)^.
Proof.
  refine (_ @ concat_p1 _).
  apply moveL_Vp.
  refine (_ @ bloop_id).
  refine ((bloop_pp _ _)^ @ _).
  apply ap, right_inverse.
Defined.

(** The underlying pointed map of [pequiv_g_loops_bg]. *)
Definition pbloop {G : Group} : G ->* loops (B G).
Proof.
  srapply Build_pMap.
  1: exact bloop.
  exact bloop_id.
Defined.

(** This says that [B] is left adjoint to the loop space functor from pointed 1-types to groups. *)
Definition pClassifyingSpace_rec {G : Group} (P : pType) `{IsTrunc 1 P}
           (bloop' : G -> loops P)
           (bloop_pp' : forall x y : G, bloop' (x * y) = bloop' x @ bloop' y)
  : B G ->* P
  := Build_pMap (ClassifyingSpace_rec P (point P) bloop' bloop_pp') idpath.

(** And this is one of the standard facts about adjoint functors: [(R h') o eta = h], where [h : G -> R P], [h' : L G -> P] is the adjunct, and eta ([bloop]) is the unit. *)
Definition pClassifyingSpace_rec_beta_bloop {G : Group} (P : pType)
  `{IsTrunc 1 P} (bloop' : G -> loops P)
  (bloop_pp' : forall x y : G, bloop' (x * y) = bloop' x @ bloop' y)
  : fmap loops (pClassifyingSpace_rec P bloop' bloop_pp') o bloop == bloop'.
Proof.
  intro x; simpl.
  refine (concat_1p _ @ concat_p1 _ @ _).
  apply ClassifyingSpace_rec_beta_bloop.
Defined.

(** Here we prove that [BG] is a delooping of [G], i.e. that [loops BG <~> G]. *)
Section EncodeDecode.

  Context `{Univalence} {G : Group}.

  Local Definition codes : B G -> HSet.
  Proof.
    srapply ClassifyingSpace_rec.
    + exact (Build_HSet G).
    + intro x.
      apply path_trunctype.
      exact (Build_Equiv _ _ (fun t => t * x) _).
    + intros x y; cbn beta.
      refine (_ @ path_trunctype_pp _ _).
      apply ap, path_equiv, path_forall.
      intro; cbn.
      apply associativity.
  Defined.

  Local Definition encode : forall b, bbase = b -> codes b.
  Proof.
    intros b p.
    exact (transport codes p mon_unit).
  Defined.

  Local Definition codes_transport
    : forall x y : G, transport codes (bloop x) y = y * x.
  Proof.
    intros x y.
    lhs napply (transport_idmap_ap _ (bloop x)).
    rhs_V rapply (transport_path_universe (.* x)).
    napply (transport2 idmap).
    lhs napply (ap_compose _ trunctype_type (bloop x)).
    rhs_V napply ap_trunctype; apply ap.
    napply ClassifyingSpace_rec_beta_bloop.
  Defined.

  Local Definition decode : forall (b : B G), codes b -> bbase = b.
  Proof.
    srapply ClassifyingSpace_ind_hset.
    + exact bloop.
    + intro x.
      apply dp_arrow.
      intro y; cbn in *.
      apply dp_paths_r.
      refine ((bloop_pp _ _)^ @ _).
      symmetry.
      apply ap, codes_transport.
  Defined.

  Local Lemma decode_encode : forall b p, decode b (encode b p) = p.
  Proof.
    intros b p.
    destruct p.
    exact bloop_id.
  Defined.

  #[export] Instance isequiv_bloop : IsEquiv (@bloop G).
  Proof.
    srapply isequiv_adjointify.
    + exact (encode _).
    + rapply decode_encode.
    + intro x.
      refine (codes_transport _ _ @ _).
      apply left_identity.
  Defined.

  (** The defining property of BG. *)
  Definition equiv_g_loops_bg : G <~> loops (B G)
    := Build_Equiv _ _ bloop _.

  (** Pointed version of the defining property. *)
  Definition pequiv_g_loops_bg : G <~>* loops (B G)
    := Build_pEquiv pbloop _.

  Definition pequiv_loops_bg_g := pequiv_g_loops_bg^-1*%equiv.

  (** We also have that the equivalence is a group isomorphism. *)

  (** First we show that the loop space of a pointed 1-type is a group. *)
  Definition LoopGroup (X : pType) `{IsTrunc 1 X} : Group
    := Build_Group (loops X) concat idpath inverse
      (Build_IsGroup _ _ _ _
        (Build_IsMonoid _ _ _
          (Build_IsSemiGroup _ _ _ concat_p_pp) concat_1p concat_p1)
        concat_Vp concat_pV).

  Definition grp_iso_g_loopgroup_bg : GroupIsomorphism G (LoopGroup (B G)).
  Proof.
    snapply Build_GroupIsomorphism'.
    1: exact equiv_g_loops_bg.
    intros x y.
    apply bloop_pp.
  Defined.

  Definition grp_iso_g_pi1_bg : GroupIsomorphism G (Pi1 (B G)).
  Proof.
    snapply (transitive_groupisomorphism _ _ _ grp_iso_g_loopgroup_bg).
    snapply Build_GroupIsomorphism'.
    - rapply equiv_tr.
    - intros x y; reflexivity.
  Defined.

  (* We also record this fact. *)
  Definition grp_homo_loops {X Y : pType} `{IsTrunc 1 X} `{IsTrunc 1 Y}
    : (X ->** Y) ->* [LoopGroup X $-> LoopGroup Y, grp_homo_const].
  Proof.
    snapply Build_pMap.
    - intro f.
      snapply Build_GroupHomomorphism.
      + exact (fmap loops f).
      + napply fmap_loops_pp.
    - cbn beta.
      apply equiv_path_grouphomomorphism.
      exact (pointed_htpy fmap_loops_pconst).
  Defined.

End EncodeDecode.

(** When [G] is an abelian group, [BG] is an H-space. *)
Section HSpace_bg.

  Context {G : AbGroup}.

  Definition bg_mul : B G -> B G -> B G.
  Proof.
    intro b.
    snapply ClassifyingSpace_rec.
    1: exact _.
    1: exact b.
    { intro x.
      revert b.
      snapply ClassifyingSpace_ind_hset.
      1: exact _.
      1: exact (bloop x).
      cbn; intro y.
      apply dp_paths_lr.
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp.
      refine ((bloop_pp _ _)^ @ _ @ bloop_pp _ _).
      apply ap, commutativity. }
    intros x y.
    revert b.
    srapply ClassifyingSpace_ind_hprop.
    exact (bloop_pp x y).
  Defined.

  Definition bg_mul_symm : forall x y, bg_mul x y = bg_mul y x.
  Proof.
    intros x.
    srapply ClassifyingSpace_ind_hset.
    { simpl.
      revert x.
      srapply ClassifyingSpace_ind_hset.
      1: reflexivity.
      intros x.
      apply sq_dp^-1, sq_1G.
      refine (ap_idmap _ @ _^).
      napply ClassifyingSpace_rec_beta_bloop. }
    intros y; revert x.
    simpl.
    snapply ClassifyingSpace_ind_hprop.
    1: exact _.
    simpl.
    transport_paths Flr.
    apply equiv_p1_1q.
    napply ClassifyingSpace_rec_beta_bloop.
  Defined.

  Definition bg_mul_left_id
    : forall b : B G, bg_mul bbase b = b.
  Proof.
    apply bg_mul_symm.
  Defined.

  Definition bg_mul_right_id
    : forall b : B G, bg_mul b bbase = b.
  Proof.
    reflexivity.
  Defined.

  #[export] Instance ishspace_bg : IsHSpace (B G)
    := Build_IsHSpace _
          bg_mul
          bg_mul_left_id
          bg_mul_right_id.

End HSpace_bg.

(** Functoriality of B(-) *)

Instance is0functor_pclassifyingspace : Is0Functor B.
Proof.
  apply Build_Is0Functor.
  intros G H f.
  snapply pClassifyingSpace_rec.
  - exact _.
  - exact (bloop o f).
  - intros x y.
    refine (ap bloop (grp_homo_op f x y) @ _).
    apply bloop_pp.
Defined.

Definition bloop_natural (G H : Group) (f : G $-> H)
  : fmap loops (fmap B f) o bloop == bloop o f.
Proof.
  napply pClassifyingSpace_rec_beta_bloop.
Defined.

Lemma pbloop_natural (G K : Group) (f : G $-> K)
  : fmap loops (fmap B f) o* pbloop ==* pbloop o* f.
Proof.
  srapply phomotopy_homotopy_hset.
  apply bloop_natural.
Defined.

Definition natequiv_g_loops_bg `{Univalence}
  : NatEquiv ptype_group (loops o B).
Proof.
  snapply Build_NatEquiv.
  1: intros G; exact pequiv_g_loops_bg.
  snapply Build_Is1Natural.
  intros X Y f.
  symmetry.
  apply pbloop_natural.
Defined.

Instance is1functor_pclassifyingspace : Is1Functor B.
Proof.
  apply Build_Is1Functor.
  (** Action on 2-cells *)
  - intros G H f g p.
    snapply Build_pHomotopy.
    { snapply ClassifyingSpace_ind_hset.
      1: exact _.
      1: reflexivity.
      intro x.
      rapply equiv_sq_dp^-1.
      simpl.
      rewrite 2 ClassifyingSpace_rec_beta_bloop.
      apply sq_1G.
      apply ap.
      exact (p x). }
    reflexivity.
  (** Preservation of identity *)
  - intros G.
    snapply Build_pHomotopy.
    { snapply ClassifyingSpace_ind_hset.
      1: exact _.
      1: reflexivity.
      intro x.
      rapply equiv_sq_dp^-1.
      simpl.
      rewrite ClassifyingSpace_rec_beta_bloop.
      apply sq_1G.
      symmetry.
      apply ap_idmap. }
    reflexivity.
  (** Preservation of composition *)
  - intros G H K g f.
    snapply Build_pHomotopy.
    { snapply ClassifyingSpace_ind_hset.
      1: exact _.
      1: reflexivity.
      intro x.
      rapply equiv_sq_dp^-1.
      simpl.
      rapply sq_ccGG.
      1,2: symmetry.
      2: refine (ap_compose (ClassifyingSpace_rec _ _ _ (fun x y =>
        ap bloop (grp_homo_op g x y) @ bloop_pp (g x) (g y))) _ (bloop x)
        @ ap _ _ @ _).
      1-3: napply ClassifyingSpace_rec_beta_bloop.
      apply sq_1G.
      reflexivity. }
    reflexivity.
Defined.

(** Interestingly, [fmap B] is an equivalence *)
Instance isequiv_fmap_pclassifyingspace `{U : Univalence} (G H : Group)
  : IsEquiv (fmap B (a := G) (b := H)).
Proof.
  snapply isequiv_adjointify.
  { intros f.
    refine (grp_homo_compose (grp_iso_inverse _) (grp_homo_compose _ _)).
    1,3: exact grp_iso_g_loopgroup_bg.
    exact (grp_homo_loops f). }
  { intros f.
    rapply equiv_path_pforall.
    snapply Build_pHomotopy.
    { snapply ClassifyingSpace_ind_hset.
      1: exact _.
      { cbn; symmetry.
        rapply (point_eq f). }
      { intro g.
        rapply equiv_sq_dp^-1.
        rewrite ClassifyingSpace_rec_beta_bloop.
        simpl.
        rapply sq_ccGc.
        1: symmetry; rapply decode_encode.
        apply equiv_sq_path.
        rewrite concat_pp_p.
        rewrite concat_pp_V.
        reflexivity. } }
      symmetry; apply concat_1p. }
  intros f.
  rapply equiv_path_grouphomomorphism.
  intro x.
  rapply (moveR_equiv_V' equiv_g_loops_bg).
  napply pClassifyingSpace_rec_beta_bloop.
Defined.

(** Hence we have that group homomorphisms are equivalent to pointed maps between their deloopings. *)
Theorem equiv_grp_homo_pmap_bg `{U : Univalence} (G H : Group)
  : (G $-> H) <~> (B G $-> B H).
Proof.
  snapply Build_Equiv.
  2: apply isequiv_fmap_pclassifyingspace.
Defined.

Instance is1natural_grp_homo_pmap_bg_r {U : Univalence} (G : Group)
  : Is1Natural (opyon G) (opyon (B G) o B) (equiv_grp_homo_pmap_bg G).
Proof.
  snapply Build_Is1Natural.
  intros K H f h.
  apply path_hom.
  rapply (fmap_comp B h f).
Defined.

Theorem natequiv_grp_homo_pmap_bg `{U : Univalence} (G : Group)
  : NatEquiv (opyon G) (opyon (B G) o B).
Proof.
  rapply Build_NatEquiv.
Defined.

(** [B(Pi 1 X) <~>* X] for a 0-connected 1-truncated [X]. *)
Theorem pequiv_pclassifyingspace_pi1 `{Univalence}
  (X : pType) `{IsConnected 0 X} `{IsTrunc 1 X}
  : B (Pi1 X) <~>* X.
Proof.
  (** The pointed map [f] is the adjunct to the inverse of the natural map [loops X -> Pi1 X]. We define it first, to make the later goals easier to read. *)
  transparent assert (f : (B (Pi1 X) ->* X)).
  { snapply pClassifyingSpace_rec.
    1: exact _.
    1: exact (equiv_tr 0 _)^-1%equiv.
    intros x y.
    strip_truncations.
    reflexivity. }
  snapply (Build_pEquiv f).
  (** [f] is an equivalence since [loops_functor f o bloop == tr^-1], and the other two maps are equivalences. *)
  apply isequiv_is0connected_isequiv_loops.
  snapply (cancelR_isequiv bloop).
  1: exact _.
  rapply isequiv_homotopic'; symmetry.
  napply pClassifyingSpace_rec_beta_bloop.
Defined.

Lemma natequiv_bg_pi1_adjoint `{Univalence} (X : pType) `{IsConnected 0 X}
  : NatEquiv (opyon (Pi1 X)) (opyon X o B).
Proof.
  nrefine (natequiv_compose (G := opyon (Pi1 (pTr 1 X))) _ _).
  2: exact (natequiv_opyon_equiv (A:=Group) (grp_iso_inverse (grp_iso_pi_Tr 0 X))).
  refine (natequiv_compose _ (natequiv_grp_homo_pmap_bg _)).
  refine (natequiv_compose (G := opyon (pTr 1 X) o B) _ _); revgoals.
  { refine (natequiv_prewhisker _ _).
    refine (natequiv_opyon_equiv _^-1$).
    rapply pequiv_pclassifyingspace_pi1. }
  snapply Build_NatEquiv.
  1: intro; exact pequiv_ptr_rec.
  exact (is1natural_prewhisker (G:=opyon X) B (opyoneda _ _ _)).
Defined.

(** The classifying space functor and the fundamental group functor form an adjunction ([pType] needs to be restricted to the subcategory of 0-connected pointed types). Note that the full adjunction should also be natural in [X], but this was not needed yet. *)
Theorem equiv_bg_pi1_adjoint `{Univalence} (X : pType)
  `{IsConnected 0 X} (G : Group)
  : (Pi 1 X $-> G) <~> (X $-> B G).
Proof.
  rapply natequiv_bg_pi1_adjoint.
Defined.

Lemma is1natural_equiv_bg_pi1_adjoint_r `{Univalence}
  (X : pType) `{IsConnected 0 X}
  : Is1Natural (opyon (Pi1 X)) (opyon X o B)
      (equiv_bg_pi1_adjoint X).
Proof.
  rapply (is1natural_natequiv (natequiv_bg_pi1_adjoint X)).
  (** Why so slow? Fixed by making this opaque. *)
  Opaque equiv_bg_pi1_adjoint.
Defined.
Transparent equiv_bg_pi1_adjoint.
