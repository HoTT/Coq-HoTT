Require Import Basics Types Pointed Cubical.
Require Import Algebra.AbGroups.
Require Import Homotopy.HSpace.
Require Import TruncType.
Require Import Truncations.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.WhiteheadsPrinciple.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.

Declare Scope bg_scope.
Local Open Scope bg_scope.

(** * We define the Classifying space of a group to be the following HIT:

  HIT ClassifyingSpace (G : Group) : 1-Type
   | bbase : ClassifyingSpace
   | bloop : X -> bbase = bbase
   | bloop_pp : forall x y, bloop (x * y) = bloop x @ bloop y.

  We implement this is a private inductive type.
*)
Module Export ClassifyingSpace.

  Section ClassifyingSpace.

    Private Inductive ClassifyingSpace (G : Group) :=
      | bbase : ClassifyingSpace G.

    Context {G : Group}.

    Axiom bloop : G -> bbase G = bbase G.

    Global Arguments bbase {_}.

    Axiom bloop_pp : forall x y, bloop (x * y) = bloop x @ bloop y.

    Global Instance istrunc_ClassifyingSpace
      : IsTrunc 1 (ClassifyingSpace G).
    Proof. Admitted.

  End ClassifyingSpace.

  Arguments ClassifyingSpace G : clear implicits.

  (** Now we can state the expected dependent elimination principle, and derive other versions of the elimination principle from it. *)
  Section ClassifyingSpace_ind.

    Local Open Scope dpath_scope.

    Context {G : Group}.

    (** Note that since our classifying space is 1-truncated, we can only eliminate into 1-truncated type families. *)
    Definition ClassifyingSpace_ind
      (P : ClassifyingSpace G -> Type)
     `{forall x, IsTrunc 1 (P x)}
      (bbase' : P bbase)
      (bloop' : forall x, DPath P (bloop x) bbase' bbase')
      (bloop_pp' : forall x y,  DPathSquare P (sq_G1 (bloop_pp x y))
        (bloop' (x * y)) ((bloop' x) @D (bloop' y)) 1 1) x : P x
      := match x with
            bbase => (fun _ _ => bbase')
         end bloop' bloop_pp'.

    (** Here we state the computation rule for [ClassifyingSpace_ind] over [bloop] as an axiom. We don't need one for bloop_pp since we have a 1-type. We leave this as admitted since the computation rule is an axiom. **)
    Definition ClassifyingSpace_ind_beta_bloop
      (P : ClassifyingSpace G -> Type)
     `{forall x, IsTrunc 1 (P x)}
      (bbase' : P bbase) (bloop' : forall x, DPath P (bloop x) bbase' bbase')
      (bloop_pp' : forall x y,  DPathSquare P (sq_G1 (bloop_pp x y))
        (bloop' (x * y)) ((bloop' x) @D (bloop' y)) 1 1) (x : G)
      : dp_apD (ClassifyingSpace_ind P bbase' bloop' bloop_pp') (bloop x)
        = bloop' x.
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
    1: intro; apply dp_const, bloop', x.
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
    rewrite <- dp_apD_const'.
    unfold ClassifyingSpace_rec.
    rewrite ClassifyingSpace_ind_beta_bloop.
    apply eissect.
  Qed.

  (** Sometimes we want to induct into a set which means we can ignore the bloop_pp arguments. Since this is a routine argument, we turn it into a special case of our induction principle. *)
  Definition ClassifyingSpace_ind_hset
    (P : ClassifyingSpace G -> Type)
   `{forall x, IsTrunc 0 (P x)}
    (bbase' : P bbase) (bloop' : forall x, DPath P (bloop x) bbase' bbase')
    : forall x, P x.
  Proof.
    refine (ClassifyingSpace_ind P bbase' bloop' _).
    intros.
    apply ds_G1, dp_path_transport.
    srapply path_ishprop.
  Defined.

  Definition ClassifyingSpace_rec_hset
    (P : Type) `{IsTrunc 0 P} (bbase' : P) (bloop' : G -> bbase' = bbase')
    : ClassifyingSpace G -> P.
  Proof.
    srapply (ClassifyingSpace_rec P bbase' bloop' _).
    intros; apply path_ishprop.
  Defined.

End Eliminators.

(** We can prove that the classifying space is 0-connected. *)
Global Instance isconnected_classifyingspace {G : Group}
  : IsConnected 0 (ClassifyingSpace G).
Proof.
  exists (tr bbase).
  srapply Trunc_ind.
  srapply ClassifyingSpace_ind_hset; cbn.
  1: reflexivity.
  intro x.
  apply dp_paths_FlFr.
  apply path_ishprop.
Defined.

(** Now we focus on the classifying space of a group. *)

(** The classifying space of a group is the following pointed type. *)
Definition pClassifyingSpace (G : Group)
  := Build_pType (ClassifyingSpace G) bbase.

(** To use the B G notation for pClassifyingSpace import this module. *)
Module Import ClassifyingSpaceNotation.
  Definition B G := pClassifyingSpace G.
End ClassifyingSpaceNotation.

Import ClassifyingSpaceNotation.

(** We can show that [bloop] takes the unit of the group to reflexivity. *)
Definition bloop_id {G : Group} : bloop (mon_unit : G) = idpath.
Proof.
  symmetry.
  apply (cancelL (bloop mon_unit)).
  refine (_ @ bloop_pp _ _).
  refine (_ @ ap _ (left_identity _)^).
  apply concat_p1.
Defined.

(** We can show that [bloop] "preserves inverses" by taking inverses in G to inverses of paths in BG *)
Definition bloop_inv {G : Group} : forall x : G, bloop (-x) = (bloop x)^.
Proof.
  intro x.
  refine (_ @ concat_p1 _).
  apply moveL_Vp.
  refine (_ @ bloop_id).
  refine ((bloop_pp _ _)^ @ _).
  apply ap, right_inverse.
Defined.

(** Here we pove that BG is the delooping of G, in that loops BG <~> G. *)
Section EncodeDecode.

  Context `{Univalence} {G : Group}.

  Local Definition codes : B G -> 0-Type.
  Proof.
    srapply ClassifyingSpace_rec.
    + srapply (BuildhSet G).
    + intro x.
      apply path_trunctype.
      apply (right_mult_equiv x).
    + intros x y.
      refine (_ @ path_trunctype_pp _ _).
      apply ap, path_equiv, path_forall.
      intro; cbn.
      apply associativity.
  Defined.

  Local Definition encode : forall z, bbase = z -> codes z.
  Proof.
    intros z p.
    exact (transport codes p mon_unit).
  Defined.

  Local Definition codes_transport
    : forall x y, transport codes (bloop x) y = y * x.
  Proof.
    intros x y.
    rewrite transport_idmap_ap.
    rewrite ap_compose.
    rewrite ClassifyingSpace_rec_beta_bloop.
    rewrite ap_trunctype.
    by rewrite transport_path_universe_uncurried.
  Qed.

  Local Definition decode : forall (z : B G), codes z -> bbase = z.
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

  Local Lemma decode_encode : forall z p, decode z (encode z p) = p.
  Proof.
    intros z p.
    destruct p.
    apply bloop_id.
  Defined.

  (** Universal property of BG *)
  Lemma equiv_loops_bg_g : loops (B G) <~> G.
  Proof.
    srapply equiv_adjointify.
    + exact (encode _).
    + exact bloop.
    + intro x.
      refine (codes_transport _ _ @ _).
      apply left_identity.
    + intro.
      apply (decode_encode bbase x).
  Defined.

  (** Pointed version of the universal property. *)
  Lemma pequiv_loops_bg_g
    : loops (B G) <~>* Build_pType G _.
  Proof.
    srapply Build_pEquiv'.
    1: apply equiv_loops_bg_g.
    reflexivity.
  Defined.

  Local Lemma encode_pp' (x : B G) (p q : bbase = x)
    : encode _ (p @ q^) = transport (fun x : B G => codes x) q^ (encode x p).
  Proof.
    destruct q; cbn.
    f_ap; apply concat_p1.
  Defined.

  Local Lemma encode_pp (p q : bbase = bbase)
    : encode _ (p @ q) = encode _ p * encode _ q.
  Proof.
    refine (_ @ codes_transport _ _).
    refine (_ @ transport2 codes _^ (encode bbase p)).
    2: rapply decode_encode.
    rewrite <- (inv_V q).
    generalize q^; intro q'; clear q.
    apply encode_pp'.
  Defined.

End EncodeDecode.

(** We also have that the equivalence is a group isomorphism. *)

(** First we show that the loop space of a pointed 1-type is a group *)
Definition LoopGroup (X : pType) `{IsTrunc 1 X} : Group
  := Build_Group (loops X) concat idpath inverse
    (Build_IsGroup _ _ _ _
      (Build_IsMonoid _ _ _
        (Build_IsSemiGroup _ _ _ concat_p_pp) concat_1p concat_p1)
      concat_Vp concat_pV).

Definition grp_iso_loopgroup_bg `{Univalence} (G : Group)
  : GroupIsomorphism (LoopGroup (B G)) G.
Proof.
  snrapply Build_GroupIsomorphism'.
  1: exact equiv_loops_bg_g.
  intros x y.
  apply encode_pp.
Defined.

(** When G is an abelian group, BG is a H-space. *)
Section HSpace_bg.

  (** TODO: funext can probably be avoided here *)
  Context `{Funext} {G : AbGroup}.

  Definition bg_mul : B G -> B G -> B G.
  Proof.
    srapply ClassifyingSpace_rec.
    1: exact idmap.
    { intro x.
      apply path_forall.
      srapply ClassifyingSpace_ind_hset.
      1: exact (bloop x).
      cbn; intro y.
      apply dp_paths_lr.
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp.
      refine ((bloop_pp _ _)^ @ _ @ bloop_pp _ _).
      apply ap, commutativity. }
    intros x y.
    rewrite <- path_forall_pp.
    apply ap; cbn.
    apply path_forall.
    srapply ClassifyingSpace_ind_hset.
    1: exact (bloop_pp x y).
    intro z.
    srapply dp_paths_FlFr_D.
    srapply path_ishprop.
  Defined.

  Definition bg_mul_beta x
    : ap (fun x0 => bg_mul x0 bbase) (bloop x) = bloop x.
  Proof.
    rewrite ap_apply_Fl.
    rewrite ClassifyingSpace_rec_beta_bloop.
    by rewrite eisretr.
  Defined.

  Definition bg_mul_symm : forall x y, bg_mul x y = bg_mul y x.
  Proof.
    srapply ClassifyingSpace_ind_hset.
    { srapply ClassifyingSpace_ind_hset.
      1: reflexivity.
      intro x.
      apply sq_dp^-1, sq_1G.
      rewrite ap_idmap.
      symmetry.
      apply bg_mul_beta. }
    intro.
    apply dp_forall_domain.
    intro y; apply dp_paths_FlFr; revert y.
    srapply ClassifyingSpace_ind_hset.
    { cbn; rewrite concat_p1.
      rewrite ap_idmap.
      apply moveR_Vp.
      symmetry.
      rewrite concat_p1.
      apply bg_mul_beta. }
    intro y.
    apply dp_paths_FlFr_D.
    apply path_ishprop.
  Defined.

  Definition bg_mul_left_id
    : forall a : B G, bg_mul (point (B G)) a = a.
  Proof.
    srapply ClassifyingSpace_ind_hset.
    1: reflexivity.
    intro; cbn; apply dp_paths_lr.
    refine (concat_pp_p _ _ _ @ _).
    apply moveR_Vp.
    refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition bg_mul_right_id
    : forall a : B G, bg_mul a (point (B G)) = a.
  Proof.
    intro.
    rewrite bg_mul_symm.
    apply bg_mul_left_id.
  Defined.

  Global Instance ishspace_bg : IsHSpace (B G)
    := Build_IsHSpace _
          bg_mul
          bg_mul_left_id
          bg_mul_right_id.

End HSpace_bg.

(** Functoriality of B(-) *)

Definition functor_pclassifyingspace {G H : Group} (f : GroupHomomorphism G H)
  : B G ->* B H.
Proof.
  snrapply Build_pMap.
  { srapply ClassifyingSpace_rec.
    1: exact (point _).
    1: exact (bloop o f).
    intros x y.
    refine (ap bloop (grp_homo_op f x y) @ _).
    apply bloop_pp. }
  reflexivity.
Defined.

Definition functor2_pclassifyingspace {G H : Group} {f g : GroupHomomorphism G H}
  : f == g -> functor_pclassifyingspace f ==* functor_pclassifyingspace g.
Proof.
  intro p.
  snrapply Build_pHomotopy.
  { srapply ClassifyingSpace_ind_hset.
    1: reflexivity.
    intro x.
    unfold functor_pclassifyingspace.
    rapply equiv_sq_dp^-1.
    simpl.
    rewrite 2 ClassifyingSpace_rec_beta_bloop.
    apply sq_1G.
    apply ap.
    exact (p x). }
  reflexivity.
Defined.

Definition functor_pclassifyingspace_idmap (G : Group)
  : functor_pclassifyingspace (@grp_homo_id G) ==* pmap_idmap.
Proof.
  snrapply Build_pHomotopy.
  { srapply ClassifyingSpace_ind_hset.
    1: reflexivity.
    intro x.
    rapply equiv_sq_dp^-1.
    simpl.
    rewrite ClassifyingSpace_rec_beta_bloop.
    apply sq_1G.
    symmetry.
    apply ap_idmap. }
  reflexivity.
Defined.

Definition functor_pclassifyingspace_compose (A B C : Group)
  (g : GroupHomomorphism A B) (f : GroupHomomorphism B C)
  : functor_pclassifyingspace (grp_homo_compose f g)
  ==* functor_pclassifyingspace f o* functor_pclassifyingspace g.
Proof.
  snrapply Build_pHomotopy.
  { srapply ClassifyingSpace_ind_hset.
    1: reflexivity.
    intro x.
    rapply equiv_sq_dp^-1.
    simpl.
    rapply sq_ccGG.
    1,2: symmetry.
    2: refine (ap_compose (ClassifyingSpace_rec _ _ _ (fun x y =>
      ap bloop (grp_homo_op g x y) @ bloop_pp (g x) (g y))) _ (bloop x)
      @ ap _ _ @ _).
    1-3: nrapply ClassifyingSpace_rec_beta_bloop.
    apply sq_1G.
    reflexivity. }
  reflexivity.
Defined.

(** Interestingly, [functor_pclassifyingspace] is an equivalence *)
Global Instance isequiv_functor_pclassifyingspace `{U : Univalence} (G H : Group)
  : IsEquiv (@functor_pclassifyingspace G H).
Proof.
  snrapply isequiv_adjointify.
  { intros f.
    refine (grp_homo_compose _ (grp_homo_compose _ (grp_iso_inverse _))).
    1,3: rapply grp_iso_loopgroup_bg.
    snrapply Build_GroupHomomorphism.
    1: by nrapply loops_functor.
    intros x y.
    apply loops_functor_pp. }
  { intros f.
    rapply equiv_path_pforall.
    snrapply Build_pHomotopy.
    { srapply ClassifyingSpace_ind_hset.
      { cbn; symmetry.
        rapply (point_eq f). }
      { intro g.
        rapply equiv_sq_dp^-1.
        unfold functor_pclassifyingspace.
        unfold Build_pMap.
        unfold pointed_fun.
        rewrite ClassifyingSpace_rec_beta_bloop.
        simpl.
        rapply sq_ccGc.
        1: symmetry; rapply decode_encode.
        apply equiv_sq_path.
        hott_simpl. } }
      symmetry; apply concat_1p. }
  intros f.
  rapply equiv_path_grouphomomorphism.
  simpl; intro g.
  rapply (moveR_equiv_M' equiv_loops_bg_g).
  rewrite concat_1p, concat_p1.
  rewrite ClassifyingSpace_rec_beta_bloop.
  reflexivity.
Defined.

(** Hence we have that group homomorphisms are equivalent to pointed maps between their deloopings. *)
Theorem equiv_grp_homo_pmap_bg `{U : Univalence} (G H : Group)
  : (GroupHomomorphism G H) <~> (B G ->* B H).
Proof.
  snrapply Build_Equiv.
  2: apply isequiv_functor_pclassifyingspace.
Defined.

(** TODO: clean up and speed up *)
(** Using Whitehead's principle we can prove that B(Pi 1 X) = X for a 0-connected 1-truncated X. *)
Theorem pequiv_pclassifyingspace_pi1 `{Univalence}
  (X : pType) `{IsConnected 0 X} `{IsTrunc 1 X}
  : B (Pi1 X) <~>* X.
Proof.
  snrapply Build_pEquiv'.
  { snrapply Build_Equiv.
    (** First we give the map inducing equivalences between homotopy groups. *)
    { srapply ClassifyingSpace_rec.
      1: exact (point _).
      { apply Trunc_rec.
        exact idmap. }
      intros x y.
      strip_truncations.
      reflexivity. }
    (** Now we apply Whitehead's principle *)
    snrapply whiteheads_principle.
    1: exact _.
    1: exact 1.
    1,2: exact _.
    1: apply isequiv_contr_contr.
    (** We need to show that this map induces equivalences for all homotopy groups *)
    intros x n.
    revert x.
    snrapply ClassifyingSpace_ind_hset.
    1: exact _.
    2: intro x; apply equiv_dp_path_transport, path_ishprop.
    hnf.
    unfold pmap_from_point.
    unfold Build_pMap.
    (** The case for n = 1 follows from the universal property of BG *)
    destruct n.
    { simpl.
      snrapply isequiv_homotopic'.
      { simpl.
        transitivity (loops (pClassifyingSpace (Pi1 X))).
        1: symmetry; rapply equiv_tr.
        rapply equiv_loops_bg_g. }
      intro x.
      strip_truncations.
      simpl.
      unfold Trunc_functor.
      unfold O_functor.
      unfold O_rec.
      simpl.
      revert x.
      snrapply equiv_ind.
      2: apply equiv_loops_bg_g.
      1: exact _.
      intro p.
      simpl.
      rewrite ClassifyingSpace_rec_beta_bloop.
      unfold encode.
      rewrite codes_transport.
      strip_truncations.
      apply path_Tr, tr.
      hott_simpl. }
    (** The case for n > 1 follows since higher homotopy groups are trivial *)
    snrapply isequiv_contr_contr.
    { nrapply contr_equiv'.
      { apply equiv_tr.
        Search IsTrunc Contr.
        nrapply trunc_contr.
        apply equiv_istrunc_contr_iterated_loops.
        snrapply trunc_leq.
        1: exact 1.
        { induction n.
          1: exact tt.
          rapply trunc_index_leq_transitive. }
        exact _. }
      apply equiv_istrunc_contr_iterated_loops.
      induction n; exact _. }
    { nrapply contr_equiv'.
      { apply equiv_tr.
        Search IsTrunc Contr.
        nrapply trunc_contr.
        apply equiv_istrunc_contr_iterated_loops.
        snrapply trunc_leq.
        1: exact 1.
        { induction n.
          1: exact tt.
          rapply trunc_index_leq_transitive. }
        exact _. }
      apply equiv_istrunc_contr_iterated_loops.
      induction n; exact _. } }
  (** Finally we need to show that this equivalence is pointed *)
  reflexivity.
Defined.
