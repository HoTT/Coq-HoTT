Require Import Basics Types HSet HFiber Limits.Pullback.
Require Import WildCat Pointed.Core Homotopy.ExactSequence.
Require Import Groups.QuotientGroup.
Require Import AbGroups.AbelianGroup AbGroups.AbPullback AbGroups.Biproduct.
Require Import AbSES.Core AbSES.Pullback. 
Require Import Modalities.Identity Modalities.Modality Truncations.Core.

Local Open Scope pointed_scope.
Local Open Scope mc_add_scope.

(** * The fiber sequence induced by pulling back along a short exact sequence *)

(** We show that pulling back along a short exact sequence [E : AbSES C B] produces a fiber sequence [AbSES C A -> AbSES E A -> AbSES B A]. The associated long exact sequence of homotopy groups recovers the usual (contravariant) six-term exact sequence of Ext groups.

We will prove the analog of exactness in terms of path data, and deduce the usual notion. *)

(** If a short exact sequence [A -> F -> E] becomes trivial after pulling back along an inclusion [i : B -> E], then there is a "transpose" short exact sequence [B -> F -> F/B]. We begin by constructing the the map [B -> F]. *)
Definition abses_pullback_inclusion_transpose_map {A B E : AbGroup}
      (i : B $-> E) `{IsEmbedding i}
      (F : AbSES E A) (p : abses_pullback i F $== pt)
  : B $-> F
  := grp_pullback_pr1 _ _ $o p^$.1 $o ab_biprod_inr.

(** The comparison map [A + B $-> F] is an embedding.  This comes up twice so we factor it out as a lemma. *)
Local Instance abses_pullback_inclusion_lemma {A B E : AbGroup}
      (i : B $-> E) `{IsEmbedding i}
      (F : AbSES E A) (p : abses_pullback i F $== pt)
  : IsEmbedding (grp_pullback_pr1 _ _ $o p^$.1).
Proof.
  nrapply (istruncmap_compose (-1) p^$.1 (grp_pullback_pr1 (projection F) i)).
  all: rapply istruncmap_mapinO_tr.
Defined.

(** The map [B -> F] is an inclusion. *)
Local Instance abses_pullback_inclusion_transpose_embedding {A B E : AbGroup}
      (i : B $-> E) `{IsEmbedding i}
      (F : AbSES E A) (p : abses_pullback i F $== pt)
  : IsEmbedding (abses_pullback_inclusion_transpose_map i F p).
Proof.
  rapply (istruncmap_compose _ (ab_biprod_inr)).
Defined.

(** We define the cokernel [F/B], which is what we need below. *)
Definition abses_pullback_inclusion_transpose_endpoint' {A B E : AbGroup}
           (i : B $-> E) `{IsEmbedding i}
           (F : AbSES E A) (p : abses_pullback i F $== pt)
  : AbGroup
  := ab_cokernel_embedding (abses_pullback_inclusion_transpose_map i F p).

(** The composite map [B -> F -> E] is homotopic to the original inclusion [i : B -> E]. *)
Lemma abses_pullback_inclusion_transpose_beta {A B E : AbGroup}
      (i : B $-> E) `{IsEmbedding i}
      (F : AbSES E A) (p : abses_pullback i F $== pt)
  : projection F $o (abses_pullback_inclusion_transpose_map i F p) == i.
Proof.
  intro b.
  change b with (ab_biprod_pr2 (A:=A) (mon_unit, b)).
  refine (pullback_commsq _ _ _ @ ap i _).
  exact (snd p^$.2 _)^.
Defined.

(** Short exact sequences in the fiber of [inclusion E] descend along [projection E]. *)
Definition abses_pullback_trivial_preimage `{Univalence} {A B C : AbGroup} (E : AbSES C B)
           (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
  : AbSES C A.
Proof.
  snrapply Build_AbSES.
  - exact (abses_pullback_inclusion_transpose_endpoint' (inclusion E) F p).
  - exact (grp_quotient_map $o inclusion F).
  - srapply (ab_cokernel_embedding_rec _ (projection E $o projection F)).
    intro b.
    refine (ap (projection E) (abses_pullback_inclusion_transpose_beta (inclusion E) F p b) @ _).
    apply iscomplex_abses.
  - apply isembedding_grouphomomorphism.
    intros a q0.
    (* Since [inclusion F a] is killed by [grp_quotient_map], its in the image of [B]. *)
    pose proof (in_coset := related_quotient_paths _ _ _ q0).
    (* Cleaning up the context facilitates later steps. *)
    destruct in_coset as [b q1]; rewrite grp_unit_r in q1.
    (* Since both [inclusion F] and [B -> F] factor through the mono [ab_biprod A B -> F], we can lift [q1] to [ab_biprod A B]. *)
    assert (q2 : ab_biprod_inr  b = ab_biprod_inl (-a)).
    1: { apply (isinj_embedding (grp_pullback_pr1 _ _ $o p^$.1)).
         - apply abses_pullback_inclusion_lemma. exact _.
         - nrefine (q1 @ _); symmetry.
           refine (ap (grp_pullback_pr1 _ _) (fst p^$.2 (-a)) @ _).
           exact (grp_homo_inv _ _). }
    (* Using [q2], we conclude. *)
    pose proof (q3 := ap (-) (fst ((equiv_path_prod _ _)^-1 q2))); cbn in q3.
    exact ((inverse_involutive _)^ @ q3^ @ grp_inv_unit).
  - apply (cancelR_conn_map (Tr (-1)) grp_quotient_map).
    1: exact _.
    simpl.
    exact _.
  - snrapply Build_IsExact.
    + srapply phomotopy_homotopy_hset.
      intro a; simpl.
      refine (ap (projection E) _ @ _).
      1: apply iscomplex_abses.
      apply grp_homo_unit.
    + intros [y q].
      apply (@contr_inhabited_hprop _ _).
      (* We choose a preimage by [grp_quotient_map]. *)
      assert (f : merely (hfiber grp_quotient_map y)).
      1: apply center, issurj_class_of.
      revert_opaque f; apply Trunc_rec; intros [f q0].
      (* Since [projection F f] is in the kernel of [projection E], we find a preimage in [B]. *)
      assert (b : merely (hfiber (inclusion E) (projection F f))).
      1: { rapply isexact_preimage.
           exact (ap _ q0 @ q). }
      revert_opaque b; apply Trunc_rec; intros [b q1].
      (* The difference [f - b] in [F] is in the kernel of [projection F], hence lies in [A]. *)
      assert (a : merely (hfiber (inclusion F)
                                 (sg_op f (-(grp_pullback_pr1 _ _ (p^$.1 (ab_biprod_inr b))))))).
      1: { rapply isexact_preimage.
           refine (grp_homo_op _ _ _ @ _).
           refine (ap (fun x => _ + x) (grp_homo_inv _ _) @ _).
           refine (ap (fun x => _ - x) (abses_pullback_inclusion_transpose_beta (inclusion E) F p b @ q1) @ _).
           apply right_inverse. }
      revert_opaque a; apply Trunc_rec; intros [a q2].
      (* It remains to show that [a] is the desired preimage. *)
      refine (tr (a; _)).
      let T := type of y in apply (@path_sigma_hprop T).
      1: intros ?; apply istrunc_paths; apply group_isgroup.
      refine (ap grp_quotient_map q2 @ _ @ q0).
      refine (grp_homo_op _ _ _ @ _).
      apply grp_moveR_Mg.
      refine (_ @ (left_inverse _)^).
      apply qglue.
      exists b.
      refine (_ @ (grp_unit_r _)^).
      exact (inverse_involutive _)^.
Defined.

(** That [abses_pullback_trivial_preimage E F p] pulls back to [F] is immediate from [abses_pullback_component1_id] and the following map. As such, we've shown that sequences which become trivial after pulling back along [inclusion E] are in the image of pullback along [projection E]. *)

Definition abses_pullback_inclusion0_map' `{Univalence} {A B C : AbGroup} (E : AbSES C B)
           (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
  : AbSESMorphism F (abses_pullback_trivial_preimage E F p).
Proof.
  srapply Build_AbSESMorphism.
  - exact grp_homo_id.
  - exact grp_quotient_map.
  - exact (projection E).
  - reflexivity.
  - reflexivity.
Defined.

(** For exactness we need not only a preimage of [F] but a preimage of [(F,p)] along [cxfib]. We now define and prove this in terms of path data. *)

(** The analog of [cxfib] induced by pullback in terms of path data. *)
Definition cxfib' {A B C : AbGroup} (E : AbSES C B)
  : AbSES C A -> graph_hfiber (abses_pullback (A:=A) (inclusion E)) pt.
Proof.
  intro Y.
  exists (abses_pullback (projection E) Y).
  refine (abses_pullback_compose' _ _ Y $@ _).
  refine (abses_pullback_homotopic' _ grp_homo_const _ Y $@ _).
  1: rapply iscomplex_abses.
  symmetry; apply abses_pullback_const'.
Defined.

Definition hfiber_cxfib' {A B C : AbGroup} (E : AbSES C B)
           (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
  := {Y : AbSES C A & hfiber_abses_path (cxfib' E Y) (F; p)}.

(* This is just [idpath], but Coq takes too long to see that. *)
Local Definition pr2_cxfib' `{Univalence} {A B C : AbGroup} {E : AbSES C B} (U : AbSES C A)
  : equiv_ptransformation_phomotopy (iscomplex_abses_pullback' _ _ (iscomplex_abses E)) U
    = equiv_path_abses_iso (cxfib' E U).2.
Proof.
  change (equiv_ptransformation_phomotopy (iscomplex_abses_pullback' _ _ (iscomplex_abses E)) U)
    with (equiv_path_abses_iso ((iscomplex_abses_pullback' _ _ (iscomplex_abses E)).1 U)).
  apply (ap equiv_path_abses_iso).
  rapply path_hom.
  refine (_ $@R abses_pullback_compose' (inclusion E) (projection E) U);
    unfold trans_comp.
  refine (_ $@R abses_pullback_homotopic' (projection E $o inclusion E) grp_homo_const (iscomplex_abses E) U).
  reflexivity.
Defined.

(** Making [abses_pullback'] opaque speeds up the following proof. *)
Opaque abses_pullback'.

Local Definition eq_cxfib_cxfib' `{Univalence} {A B C : AbGroup} {E : AbSES C B} (U : AbSES C A)
  : cxfib (iscomplex_pullback_abses E) U = equiv_hfiber_abses _ _ (cxfib' E U).
Proof.
  srapply path_sigma.
  1: reflexivity.
  nrefine (concat_p1 _ @ _).
  nrefine (concat_1p _ @ _).
  cbn zeta.
  unfold equiv_hfiber_abses, equiv_functor_sigma_id, equiv_functor_sigma', equiv_functor_sigma, equiv_fun, functor_sigma, ".2".
  (* The goal looks identical to [pr2_cxfib'], but the implicit argument to [@paths] is expressed differently, which is why the next line isn't faster. *)
  exact (@pr2_cxfib' _ A B C E U).
Defined.

Transparent abses_pullback'.

Definition equiv_hfiber_cxfib' `{Univalence} {A B C : AbGroup} {E : AbSES C B}
           (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
  : hfiber_cxfib' E F p <~> hfiber (cxfib (iscomplex_pullback_abses E))
                  (equiv_hfiber_abses _ pt (F;p)).
Proof.
  srapply equiv_functor_sigma_id; intro U; lazy beta.
  refine (_ oE equiv_hfiber_abses_pullback _ _ _).
  refine (_ oE equiv_ap' (equiv_hfiber_abses _ pt) _ _).
  apply equiv_concat_l.
  apply eq_cxfib_cxfib'.
Defined.

(** The type of paths in [hfiber_cxfib'] in terms of path data. *)
Definition path_hfiber_cxfib' {A B C : AbGroup} {E : AbSES C B}
           {F : AbSES (middle E) A} {p : abses_pullback (inclusion E) F $== pt}
           (X Y : hfiber_cxfib' (B:=B) E F p)
  : Type.
Proof.
  refine (sig (fun q0 : X.1 $== Y.1 => _)).
  exact ((fmap (abses_pullback (projection E)) q0)^$ $@ X.2.1 $== Y.2.1).
Defined.

Definition transport_hfiber_abses_path_cxfib'_l `{Univalence} {A B C : AbGroup} {E : AbSES C B}
           (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
           (U V : hfiber_cxfib' E F p) (q : U.1 = V.1)
  : (transport (fun Y : AbSES C A => hfiber_abses_path (cxfib' E Y) (F; p)) q U.2).1
    = fmap (abses_pullback (projection E)) (equiv_path_abses_iso^-1 q^) $@ U.2.1.
Proof.
  induction q.
  refine (ap pr1 (transport_1 _ _) @ _).
  refine (_ @ ap (fun x => fmap (abses_pullback (projection E)) x $@ _) equiv_path_absesV_1^).
  refine (_ @ ap (fun x => x $@ _) (fmap_id_strong _ _)^).
  exact (cat_idr_strong _)^.
Defined.

Definition equiv_path_hfiber_cxfib' `{Univalence} {A B C : AbGroup} {E : AbSES C B}
           (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
           (U V : hfiber_cxfib' E F p)
  : path_hfiber_cxfib' U V <~> U = V.
Proof.
  refine (equiv_path_sigma _ _ _ oE _).
  srapply (equiv_functor_sigma' equiv_path_abses_iso);
    intro q; lazy beta.
  refine (equiv_path_sigma_hprop _ _ oE _).
  refine (equiv_concat_l _ _ oE _).
  1: apply transport_hfiber_abses_path_cxfib'_l.
  refine (equiv_path_sigma_hprop _ _ oE equiv_concat_l _ _ oE _).
  1: { refine (ap (fun x => (fmap (abses_pullback _) x $@ _).1) _).
       nrefine (ap _ (abses_path_data_V q) @ _).
       apply eissect. }
  refine (equiv_concat_l _ _ oE _).
  1: { refine (ap (fun x => (x $@ _).1) _).
       rapply gpd_strong_1functor_V. }
  apply equiv_path_groupisomorphism.
Defined.

(** The fibre of [cxfib'] over [(F;p)] is inhabited. *)
Definition hfiber_cxfib'_inhabited `{Univalence} {A B C : AbGroup} (E : AbSES C B)
      (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
  : hfiber_cxfib' E F p.
Proof.
  exists (abses_pullback_trivial_preimage E F p).
  srefine (_^$; _).
  1: by rapply (abses_pullback_component1_id' (abses_pullback_inclusion0_map' E F p)).
  lazy beta; unfold pr2.
  refine (cat_assoc _ _ _ $@ _).
  refine (cat_assoc _ _ _ $@ _).
  apply gpd_moveR_Vh.
  apply gpd_moveL_hM.
  apply equiv_ab_biprod_ind_homotopy.
  split; apply equiv_path_pullback_rec_hset; split; cbn.
  - intro a.
    exact (ap (class_of _ o pullback_pr1) (fst p^$.2 a)).
  - intro a.
    exact ((snd p^$.2 _)^).
  - intro b; apply qglue.
    exists (-b).
    apply grp_moveL_Vg.
    refine ((grp_homo_op (grp_pullback_pr1 _ _ $o p^$.1 $o ab_biprod_inr) _ _)^ @ _).
    exact (ap _ (right_inverse _) @ grp_homo_unit _ @ (grp_homo_unit _)^).
  - intro b.
    exact (snd p^$.2 _)^.
Defined.

(** To conclude exactness in terms of path data, we show that the fibre is a proposition, hence contractible. *)

(** Given a point [(Y;Q)] in the fiber of [cxfib'] over [(F;p)] there is an induced map as follows. *)
Local Definition hfiber_cxfib'_induced_map {A B C : AbGroup} (E : AbSES C B)
      (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
      (Y : hfiber_cxfib' E F p)
  : ab_biprod A B $-> abses_pullback (projection E) Y.1.
Proof.
  destruct Y as [Y q].
  refine (grp_homo_compose _ (grp_iso_inverse p.1)).
  refine (_ $o grp_pullback_pr1 _ _).
  exact (q.1^$.1).
Defined.

(** There is "another" obvious induced map. *)
Definition abses_pullback_splits_induced_map' {A B C : AbGroup}
           (E : AbSES C B) (Y : AbSES C A)
  : ab_biprod A B $-> abses_pullback (projection E) Y.
Proof.
  srapply (ab_biprod_rec (inclusion _)).
  srapply grp_pullback_corec.
  - exact grp_homo_const.
  - exact (inclusion E).
  - intro x.
    refine (grp_homo_unit _ @ _).
    symmetry; apply iscomplex_abses.
Defined.

Lemma fmap_hfiber_abses_lemma `{Univalence} {A B B' : AbGroup} (f : B' $-> B)
           (X Y : graph_hfiber (abses_pullback (A:=A) f) pt) (Q : hfiber_abses_path X Y)
  : fmap (abses_pullback f) Q.1^$ $o Y.2^$ $== X.2^$.
Proof.
  generalize Q.
  equiv_intro (equiv_hfiber_abses_pullback _ X Y)^-1%equiv p;
    induction p.
  refine ((_ $@R _) $@ _).
  { Unshelve.
    2: exact (Id _).
    refine (fmap2 _ _ $@ fmap_id _ _).
    intro x; reflexivity. }
  exact (cat_idl _).
Defined.

Lemma induced_map_eq `{Univalence} {A B C : AbGroup} (E : AbSES C B)
      (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
      (Y : hfiber_cxfib' E F p)
  : hfiber_cxfib'_induced_map E F p Y == abses_pullback_splits_induced_map' E Y.1.
Proof.
  intros [a b]; cbn.
  refine (ap pullback_pr1 (fmap_hfiber_abses_lemma _ _ (F;p) Y.2 _) @ _).
  srapply equiv_path_pullback_hset; split; cbn.
  - exact (grp_unit_r _)^.
  - exact (grp_unit_l _)^.
Defined.

(** Given another point [(Y,Q)] in the fibre of [cxfib'] over [(F;p)], we get path data in [AbSES C A]. *)
Lemma hfiber_cxfib'_induced_path'0 `{Univalence} {A B C : AbGroup} (E : AbSES C B)
      (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
      (Y : hfiber_cxfib' E F p)
  : abses_pullback_trivial_preimage E F p $== Y.1.
Proof.
  destruct Y as [Y Q].
  apply abses_path_data_to_iso;
    srefine (_; (_,_)).
  - snrapply (ab_cokernel_embedding_rec _ (grp_pullback_pr1 _ _$o (Q.1^$).1)).
    1-3: exact _.
    intro f.
    nrefine (ap _ (induced_map_eq E F p (Y;Q) _) @ _); cbn.
    exact (grp_unit_r _ @ grp_homo_unit _).
  - intro a.
    refine (_ @ ap (grp_pullback_pr1 _ _) (fst (Q.1^$).2 a)).
    exact (grp_quotient_rec_beta' _ F _ _ (inclusion F a)).
  - nrapply (conn_map_elim _ grp_quotient_map).
    1: apply issurj_class_of.
    1: intros ?; apply istrunc_paths; apply group_isgroup.
    intro f.
    refine (ap (projection E) (snd (Q.1^$).2 f) @ _); unfold pr1.
    exact (pullback_commsq _ _ ((Q.1^$).1 f))^.
Defined.

Lemma hfiber_cxfib'_induced_path' `{Univalence} {A B C : AbGroup} (E : AbSES C B)
      (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
      (Y : hfiber_cxfib' E F p)
  : path_hfiber_cxfib' (hfiber_cxfib'_inhabited E F p) Y.
Proof.
  exists (hfiber_cxfib'_induced_path'0 E F p Y).
  rapply gpd_moveR_Vh.
  rapply gpd_moveL_hM.
  rapply gpd_moveR_Vh.
  intro x.
  srapply equiv_path_pullback_hset; split.
  2: exact (snd Y.2.1^$.2 x)^.
  reflexivity.
Defined.

(** It follows that [hfiber_cxfib'] is contractible. *)
Lemma contr_hfiber_cxfib' `{Univalence} {A B C : AbGroup} (E : AbSES C B)
      (F : AbSES (middle E) A) (p : abses_pullback (inclusion E) F $== pt)
  : Contr (hfiber_cxfib' E F p).
Proof.
  srapply Build_Contr.
  1: apply hfiber_cxfib'_inhabited.
  intros [Y q].
  apply equiv_path_hfiber_cxfib'.
  apply hfiber_cxfib'_induced_path'.
Defined.

(** From this we deduce exactness. *)
Global Instance isexact_abses_pullback `{Univalence} {A B C : AbGroup} {E : AbSES C B}
  : IsExact purely (abses_pullback_pmap (A:=A) (projection E)) (abses_pullback_pmap (inclusion E)).
Proof.
  srapply Build_IsExact.
  1: apply iscomplex_pullback_abses.
  srapply (equiv_ind (equiv_hfiber_abses (abses_pullback (inclusion E)) (point (AbSES B A)))).
  intros [F p].
  rapply contr_equiv'.
  1: apply equiv_hfiber_cxfib'.
  apply contr_hfiber_cxfib'.
Defined.
