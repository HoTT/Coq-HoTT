From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core Universe Equiv.
Require Import Pointed.
Require Import Cubical.DPath.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import Homotopy.Suspension.
Require Import Homotopy.ClassifyingSpace.
Import ClassifyingSpaceNotation.
Require Import Homotopy.HSpace.Coherent.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.Hopf.
Require Import Truncations.Core Truncations.Connectedness.

(** * Eilenberg-Mac Lane spaces *)

Local Open Scope pointed_scope.
Local Open Scope nat_scope.
Local Open Scope mc_mult_scope.

(** The definition of the Eilenberg-Mac Lane spaces.  Note that while we allow [G] to be non-abelian for [n > 1], later results will need to assume that [G] is abelian. *)
Fixpoint EilenbergMacLane@{u v | u <= v} (G : Group@{u}) (n : nat) : pType@{v}
  := match n with
      | 0    => G
      | 1    => pClassifyingSpace@{u v} G
      | m.+1 => pTr m.+1 (psusp (EilenbergMacLane G m))
     end.

Notation "'K(' G , n )" := (EilenbergMacLane G n).

Section EilenbergMacLane.
  Context `{Univalence}.

  #[export] Instance istrunc_em {G : Group} {n : nat} : IsTrunc n K(G, n).
  Proof.
    destruct n as [|[]]; exact _.
  Defined.

  (** This is subsumed by the next result, but Coq doesn't always find the next result when it should. *)
  #[export] Instance isconnected_em {G : Group} (n : nat)
    : IsConnected n K(G, n.+1).
  Proof.
    induction n; exact _.
  Defined.

  #[export] Instance isconnected_em' {G : Group} (n : nat)
    : IsConnected n.-1 K(G, n).
  Proof.
    destruct n.
    1: exact (is_minus_one_connected_pointed _).
    apply isconnected_em.
  Defined.

  #[export] Instance is0connected_em {G : Group} (n : nat)
    : IsConnected 0 K(G, n.+1).
  Proof.
    rapply (is0connected_isconnected n.-2).
  Defined.

  Local Open Scope trunc_scope.

  (** This is a variant of [pequiv_ptr_loop_psusp] from pSusp.v. All we are really using is that [n.+2 <= n +2+ n], but because of the use of [isconnmap_pred_add], the proof is a bit more specific to this case. *)
  Local Lemma pequiv_ptr_loop_psusp' (X : pType) (n : nat) `{IsConnected n.+1 X}
    : pTr n.+2 X <~>* pTr n.+2 (loops (psusp X)).
  Proof.
    snapply Build_pEquiv.
    1: exact (fmap (pTr _) (loop_susp_unit _)).
    napply O_inverts_conn_map.
    napply (isconnmap_pred_add n.-2).
    rewrite 2 trunc_index_add_succ.
    exact (conn_map_loop_susp_unit n X).
  Defined.

  Lemma pequiv_loops_em_em (G : AbGroup) (n : nat)
    : K(G, n) <~>* loops K(G, n.+1).
  Proof.
    destruct n.
    1: exact pequiv_g_loops_bg.
    change (K(G, n.+1) <~>* loops (pTr n.+2 (psusp (K(G, n.+1))))).
    refine (ptr_loops _ _ o*E _).
    destruct n.
    1: srapply (licata_finster (m:=-2)).
    refine (_ o*E pequiv_ptr (n:=n.+2)).
    rapply pequiv_ptr_loop_psusp'.
  Defined.

  Definition pequiv_loops_em_g (G : AbGroup) (n : nat)
    : G <~>* iterated_loops n K(G, n).
  Proof.
    induction n.
    - exact pequiv_pmap_idmap.
    - refine ((unfold_iterated_loops' _ _)^-1* o*E _ o*E IHn).
      exact (emap (iterated_loops n) (pequiv_loops_em_em _ _)).
  Defined.

  (** For positive indices, we in fact get a group isomorphism. *)
  Definition equiv_g_pi_n_em (G : AbGroup) (n : nat)
    : GroupIsomorphism G (Pi n.+1 K(G, n.+1)).
  Proof.
    induction n.
    - exact grp_iso_g_pi1_bg.
    - nrefine (grp_iso_compose _ IHn).
      nrefine (grp_iso_compose _ (groupiso_pi_functor _ (pequiv_loops_em_em _ _))).
      symmetry; exact (groupiso_pi_loops _ _).
  Defined.

  Definition iscohhspace_em {G : AbGroup} (n : nat)
    : IsCohHSpace K(G, n).
  Proof.
    napply iscohhspace_equiv_cohhspace.
    2: apply pequiv_loops_em_em.
    exact iscohhspace_loops.
  Defined.

  (** If [G] and [G'] are isomorphic, then [K(G,n)] and [K(G',n)] are equivalent.  This also follows from [em_fmap] below. *)
  Definition pequiv_em_group_iso {G G' : Group} (n : nat)
    (e : G $<~> G')
    : K(G, n) <~>* K(G', n).
  Proof.
    by destruct (equiv_path_group e).
  Defined.

  (** The action of [K(-,n)] on group homomorphisms, giving the functoriality
      of [K(-,n)].  Note that [fmap B] and the WildCat functoriality of
      [psusp] and [pTr] constrain the two groups to a single universe. *)
  Definition em_fmap {G G' : AbGroup} (f : GroupHomomorphism G G') (n : nat)
    : K(G, n) ->* K(G', n).
  Proof.
    induction n as [|n IHn].
    - exact (Build_pMap f (grp_homo_unit f)).
    - destruct n as [|m].
      + exact (fmap B f).
      + exact (fmap (pTr m.+2) (fmap psusp IHn)).
  Defined.

  (** [em_fmap] preserves the identity. *)
  Definition em_fmap_idmap {G : AbGroup} (n : nat)
    : em_fmap (G:=G) grp_homo_id n ==* pmap_idmap.
  Proof.
    induction n as [|[|m] IH].
    - snapply Build_pHomotopy.
      + reflexivity.
      + rapply path_ishprop.
    - exact (fmap_id B G).
    - refine (_ @* fmap_id (pTr m.+2) _).
      tapply (fmap2 (pTr m.+2)).
      refine (_ @* fmap_id psusp _).
      tapply (fmap2 psusp).
      exact (pointed_htpy IH).
  Defined.

  (** [em_fmap] preserves composition. *)
  Definition em_fmap_compose {G G' G'' : AbGroup}
    (f : GroupHomomorphism G G') (g : GroupHomomorphism G' G'') (n : nat)
    : em_fmap (grp_homo_compose g f) n ==* em_fmap g n o* em_fmap f n.
  Proof.
    induction n as [|[|m] IH].
    - snapply Build_pHomotopy.
      + reflexivity.
      + rapply path_ishprop.
    - exact (fmap_comp B f g).
    - refine (_ @* fmap_comp (pTr m.+2) _ _).
      tapply (fmap2 (pTr m.+2)).
      refine (_ @* fmap_comp psusp _ _).
      tapply (fmap2 psusp).
      exact (pointed_htpy IH).
  Defined.

  (** At positive levels, [pequiv_loops_em_em] is the canonical comparison
      map: the loop-suspension unit followed by [loops] of the truncation
      map.  This presentation makes its naturality transparent, without
      reference to the Hopf-construction input used to show that it is an
      equivalence. *)
  Definition loops_em_em_ptr_unit (G : AbGroup) (n : nat)
    : pequiv_loops_em_em G n.+1
      ==* fmap loops ptr o* loop_susp_unit K(G, n.+1).
  Proof.
    destruct n as [|n].
    all: refine (compose_cate_fun (A:=pType) _ _ @* _).
    all: refine (pmap_postwhisker _ (compose_cate_fun (A:=pType) _ _) @* _).
    1: refine (pmap_postwhisker _ (pto_O_natural (Tr _) _) @* _).
    2: refine (pmap_postwhisker _ (ptr_natural _ _) @* _).
    all: refine ((pmap_compose_assoc _ _ _)^* @* _).
    all: exact (pmap_prewhisker _ (ptr_loops_commutes _ _)).
  Defined.

  (** [em_fmap] commutes with the loop-space identifications, so it is a
      map of spectra. *)
  Definition em_fmap_loops_natural {G G' : AbGroup}
    (f : GroupHomomorphism G G') (n : nat)
    : fmap loops (em_fmap f n.+1) o* pequiv_loops_em_em G n
      ==* pequiv_loops_em_em G' n o* em_fmap f n.
  Proof.
    destruct n as [|n].
    - exact (pbloop_natural G G' f).
    - refine (pmap_postwhisker _ (loops_em_em_ptr_unit G n) @* _).
      refine (_ @* pmap_prewhisker _ (loops_em_em_ptr_unit G' n)^*).
      refine ((pmap_compose_assoc _ _ _)^* @* _).
      refine (pmap_prewhisker _ (fmap_comp loops _ _)^* @* _).
      refine (pmap_prewhisker _ (fmap2 loops (ptr_natural _ _)) @* _).
      refine (pmap_prewhisker _ (fmap_comp loops _ _) @* _).
      refine (pmap_compose_assoc _ _ _ @* _).
      refine (pmap_postwhisker _ (loop_susp_unit_natural _)^* @* _).
      exact (pmap_compose_assoc _ _ _)^*.
  Defined.

  (** [equiv_g_pi_n_em] at level [n.+1] unfolds to the level-[n] map
      conjugated by [groupiso_pi_loops] and [pequiv_loops_em_em]. *)
  Local Definition equiv_g_pi_n_em_succ (G : AbGroup) (n : nat) (x : G)
    : equiv_g_pi_n_em G n.+1 x
      = grp_iso_inverse (groupiso_pi_loops _ _)
          (groupiso_pi_functor _ (pequiv_loops_em_em G n.+1)
            (equiv_g_pi_n_em G n x))
    := idpath.

  (** The action of [em_fmap f n.+1] on [Pi n.+1] agrees with [f] under the
      identifications [equiv_g_pi_n_em]. *)
  Definition pi_em_fmap {G G' : AbGroup}
    (f : GroupHomomorphism G G') (n : nat)
    : fmap (Pi n.+1) (em_fmap f n.+1) o equiv_g_pi_n_em G n
      == equiv_g_pi_n_em G' n o f.
  Proof.
    induction n as [|n IHn]; intro g.
    - exact (ap tr (bloop_natural G G' f g)).
    - lhs napply (ap _ (equiv_g_pi_n_em_succ G n g)).
      rhs napply (equiv_g_pi_n_em_succ G' n (f g)).
      apply (equiv_inj (groupiso_pi_loops n _)).
      rhs napply (eisretr (groupiso_pi_loops n _) _).
      lhs napply (fmap_pi_loops n.+1 (em_fmap f n.+2) _).
      lhs napply (ap _ (eisretr (groupiso_pi_loops n _) _)).
      lhs_V exact (fmap_comp (pPi n.+1)
          (pequiv_loops_em_em G n.+1 : _ ->* _)
          (fmap loops (em_fmap f n.+2)) (equiv_g_pi_n_em G n g)).
      lhs exact (fmap2 (pPi n.+1) (em_fmap_loops_natural f n.+1)
          (equiv_g_pi_n_em G n g)).
      lhs exact (fmap_comp (pPi n.+1)
          (em_fmap f n.+1) (pequiv_loops_em_em G' n.+1 : _ ->* _)
          (equiv_g_pi_n_em G n g)).
      exact (ap _ (IHn g)).
  Defined.

  (** Eilenberg-Mac Lane spaces of a contractible group are contractible. *)
  #[export] Instance contr_em_contr {G : AbGroup} `{Contr G} (n : nat)
    : Contr K(G, n).
  Proof.
    induction n as [|[|n] IHn].
    - exact _.
    - exact _.
    - apply (Build_Contr _ (tr (center _))).
      srapply Trunc_ind; intro a.
      exact (ap tr (contr a)).
  Defined.

  (** Any pointed map into a contractible type is homotopic to the constant
      map. *)
  Local Definition phomotopy_pconst_contr {X Y : pType} `{Contr Y}
    (f : X ->* Y)
    : f ==* pconst.
  Proof.
    snapply Build_pHomotopy.
    - intro x; apply path_contr.
    - apply path_contr.
  Defined.

  (** [em_fmap] sends the constant homomorphism to the constant map. *)
  Definition em_fmap_const {G G' : AbGroup} (n : nat)
    : em_fmap (G:=G) (G':=G') grp_homo_const n ==* pconst.
  Proof.
    refine (phomotopy_path (ap (fun h => em_fmap h n) _)
            @* em_fmap_compose (G':=abgroup_trivial)
                 (grp_trivial_corec G) (grp_trivial_rec G') n
            @* pmap_postwhisker _ (phomotopy_pconst_contr _)
            @* precompose_pconst _).
    napply equiv_path_grouphomomorphism; intro x; reflexivity.
  Defined.

  (** [em_fmap f n.+1] of a surjective homomorphism is an [n]-connected
      map.  Both surjectivity of the map and of its [ap]s reduce to the
      previous level through the loop-space identifications. *)
  #[export] Instance isconnmap_em_fmap {G G' : AbGroup}
    (f : GroupHomomorphism G G') `{!IsSurjection f} (n : nat)
    : IsConnMap n (em_fmap f n.+1).
  Proof.
    induction n as [|n IHn].
    - exact (isconnmap_fmap_pclassifyingspace f).
    - snapply isconnmap_isconnmap_ap_surj.
      + rapply (isconnmap_isconnected (-1)).
      + assert (c : IsConnMap n (fmap loops (em_fmap f n.+2))).
        { napply (conn_map_homotopic _
            ((pequiv_loops_em_em G' n.+1 o* em_fmap f n.+1)
             o* (pequiv_loops_em_em G n.+1)^-1*) _
            (fun p =>
              (moveR_pequiv_fV _ _ _ (em_fmap_loops_natural f n.+1))^* p)).
          exact _. }
        snapply (conn_point_elim (-1) (A:=K(G, n.+2))).
        1,2: exact _.
        snapply (conn_point_elim (-1) (A:=K(G, n.+2))).
        1,2: exact _.
        intro q.
        pose (e2 := equiv_concat_l (point_eq (em_fmap f n.+2))^ _
                    oE equiv_concat_r (point_eq (em_fmap f n.+2)) _).
        exact (isconnected_equiv' n _
                 (equiv_functor_sigma_id (fun p => equiv_ap e2 _ _))^-1%equiv
                 (c _)).
  Defined.

  (** [em_fmap] is an equivalence from group homomorphisms to pointed maps,
      extending [isequiv_fmap_pclassifyingspace] to all levels.  In
      particular, pointed maps between Eilenberg-Mac Lane spaces of the same
      level are determined by their effect on homotopy groups. *)
  #[export] Instance isequiv_em_fmap (G G' : AbGroup) (n : nat)
    : IsEquiv (fun f : GroupHomomorphism G G' => em_fmap f n.+1).
  Proof.
    induction n as [|n IHn].
    - exact (isequiv_fmap_pclassifyingspace G G').
    - (* The ladder [pequiv_ptr_rec], [loop_susp_adjoint], postcomposition
         with [pequiv_loops_em_em], and the inductive hypothesis. *)
      pose (L := ((Build_Equiv _ _ _ IHn)^-1%equiv)
        oE (pequiv_pequiv_postcompose (pequiv_loops_em_em G' n.+1)^-1*
            : (K(G, n.+1) ->** loops K(G', n.+2)) <~> _)
        oE (loop_susp_adjoint K(G, n.+1) K(G', n.+2)
            : (psusp K(G, n.+1) ->** _) <~> _)
        oE (pequiv_ptr_rec
            : (K(G, n.+2) ->** K(G', n.+2)) <~> _)).
      napply (isequiv_homotopic' L^-1%equiv).
      intro f.
      apply moveR_equiv_V; symmetry.
      apply moveR_equiv_V.
      apply path_pforall.
      refine (pmap_postwhisker _
        (pmap_prewhisker _ (fmap2 loops (ptr_natural _ _))) @* _).
      refine (pmap_postwhisker _
        (pmap_prewhisker _ (fmap_comp loops _ _)) @* _).
      refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _) @* _).
      refine (pmap_postwhisker _
        (pmap_postwhisker _ (loop_susp_unit_natural _)^*) @* _).
      refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _)^* @* _).
      refine (pmap_postwhisker _
        (pmap_prewhisker _ (loops_em_em_ptr_unit G' n)^*) @* _).
      refine ((pmap_compose_assoc _ _ _)^* @* _).
      refine (pmap_prewhisker _ (peissect _) @* _).
      apply pmap_postcompose_idmap.
  Defined.

  (** Pointed maps between Eilenberg-Mac Lane spaces of the same level
      which agree on homotopy groups are equal. *)
  Definition path_em_pmap_pi {G G' : AbGroup} (n : nat)
    (phi psi : K(G, n.+1) ->* K(G', n.+1))
    (h : fmap (Pi n.+1) phi == fmap (Pi n.+1) psi)
    : phi = psi.
  Proof.
    pose (e := Build_Equiv _ _ _ (isequiv_em_fmap G G' n)).
    refine ((eisretr e phi)^ @ ap e _ @ eisretr e psi).
    apply equiv_path_grouphomomorphism; intro g.
    apply (equiv_inj (equiv_g_pi_n_em G' n)).
    refine ((pi_em_fmap _ n g)^ @ _ @ pi_em_fmap _ n g).
    refine (ap (fun (m : _ ->* _) => fmap (Pi n.+1) m _) (eisretr e phi) @ _).
    refine (_ @ ap (fun (m : _ ->* _) => fmap (Pi n.+1) m _) (eisretr e psi)^).
    apply h.
  Defined.

  (** [em_fmap] of a group isomorphism is a pointed equivalence. *)
  Definition pequiv_em_fmap {G G' : AbGroup}
    (e : GroupIsomorphism G G') (n : nat)
    : K(G, n) <~>* K(G', n).
  Proof.
    snapply Build_pEquiv.
    1: exact (em_fmap e n).
    snapply isequiv_adjointify.
    1: exact (em_fmap (grp_iso_inverse e) n).
    - intro x.
      lhs_V exact (em_fmap_compose (G':=G) (grp_iso_inverse e) e n x).
      refine (phomotopy_path
        (ap (fun h => em_fmap h n) (_ : _ = grp_homo_id)) x
        @ em_fmap_idmap n x).
      by apply equiv_path_grouphomomorphism; intro g; apply eisretr.
    - intro x.
      lhs_V exact (em_fmap_compose (G':=G') e (grp_iso_inverse e) n x).
      refine (phomotopy_path
        (ap (fun h => em_fmap h n) (_ : _ = grp_homo_id)) x
        @ em_fmap_idmap n x).
      by apply equiv_path_grouphomomorphism; intro g; apply eissect.
  Defined.

  (** Every pointed (n-1)-connected n-type is an Eilenberg-Mac Lane space. *)
  Definition pequiv_em_connected_truncated (X : pType)
    (n : nat) `{IsConnected n X} `{IsTrunc n.+1 X}
    : K(Pi n.+1 X, n.+1) <~>* X.
  Proof.
    generalize dependent X; induction n; intros X isC isT.
    1: rapply pequiv_pclassifyingspace_pi1.
    (* The equivalence will be the composite
<<
      K( (Pi n.+2 X) n.+2)
   <~>* K( (Pi n.+1 (loops X)), n.+2)
   = pTr n.+2 (psusp K( (Pi n.+1 (loops X)), n.+1))  [by definition]
   <~>* pTr n.+2 (psusp (loops X))                   [by induction]
   <~>* pTr n.+2 X
   <~>* X
>>
    and we'll work from right to left.
*)
    refine ((pequiv_ptr (n:=n.+2))^-1* o*E _).
    refine (pequiv_ptr_psusp_loops X n o*E _).
    change (K(?G, n.+2)) with (pTr n.+2 (psusp K( G, n.+1 ))).
    refine (emap (pTr n.+2 o psusp) _).
    refine ((IHn (loops X) _ _) o*E _).
    apply pequiv_em_group_iso.
    apply groupiso_pi_loops.
  Defined.

End EilenbergMacLane.

(** ** Delooping Eilenberg-Mac Lane mapping types *)

(** The [n.+2]-nd homotopy group of an [n.+1]-truncated type vanishes. *)
Definition contr_pi_succ_istrunc `{Univalence} (n : nat) (X : pType)
  `{IsTrunc n.+1 X}
  : Contr (Pi n.+2 X).
Proof.
  pose proof (c := equiv_istrunc_contr_iterated_loops n.+2 X _ (point _)).
  apply (Build_Contr _ (tr (center _))).
  srapply Trunc_ind; intro a.
  exact (ap tr (contr a)).
Defined.

Section Deloop.
  Context `{Univalence} (B A : AbGroup@{u}).

  (** By Freudenthal, the loop-suspension unit of [K(B,2)] is 2-connected,
      so [Pi 3] of the unit is surjective; since [Pi 3 K(B,2)] is trivial,
      [psusp K(B,2)] has trivial [Pi 4]. *)
  Local Instance contr_pi4_psusp_em : Contr (Pi 4 (psusp K(B, 2))).
  Proof.
    nrefine (contr_equiv' (Pi 3 (loops (psusp K(B, 2)))) _).
    1: exact (grp_iso_inverse (groupiso_pi_loops 2 (psusp K(B, 2)))).
    pose proof (C := @conn_map_loop_susp_unit _ 0 K(B, 2)
      (isconnected_em 1)
      : IsConnMap 2 (loop_susp_unit K(B, 2))).
    pose proof (contr_pi_succ_istrunc 1 K(B, 2)).
    pose proof (S := issurj_pi_connmap 2 (loop_susp_unit K(B, 2))).
    pose (fu := fmap (pPi 3) (loop_susp_unit K(B, 2))
      : Pi 3 K(B, 2) -> Pi 3 (loops (psusp K(B, 2)))).
    apply (Build_Contr _ (fu (center _))).
    intro y.
    pose proof (m := @center _ (S y)).
    strip_truncations.
    destruct m as [x p].
    refine (_ @ p).
    exact (ap _ (path_contr _ x)).
  Defined.

  (** Hence the 4-truncation of [psusp K(B,2)] is already 3-truncated. *)
  Local Instance istrunc_ptr4_psusp_em
    : IsTrunc 3 (pTr 4 (psusp K(B, 2))).
  Proof.
    apply (equiv_istrunc_contr_iterated_loops 4 _)^-1.
    pose proof (@isconnected_susp 1 K(B, 2) (isconnected_em 1)).
    pose proof (is0connected_isconnected 0 (psusp K(B, 2))).
    pose proof (isconnected_trunc 0 4 (X := psusp K(B, 2))).
    snapply (conn_point_elim (-1)).
    1,2: exact _.
    nrefine (contr_equiv' (Pi 4 (pTr 4 (psusp K(B, 2)))) _).
    1: exact (equiv_tr 0 _)^-1%equiv.
    nrefine (contr_equiv' (Pi 4 (psusp K(B, 2))) _).
    1: exact (grp_iso_pi_Tr 3 (psusp K(B, 2))).
    exact _.
  Defined.

  (** [K(B,3)] sits inside the 3-truncation of [pTr 4 (psusp K(B,2))]
      via [fmap (pTr 3) ptr]; this is an equivalence since the source is
      already 3-truncated. *)
  Local Definition pequiv_ptr3_ptr4_psusp_em
    : K(B, 3) <~>* pTr 3 (pTr 4 (psusp K(B, 2))).
  Proof.
    snapply Build_pEquiv.
    1: exact (fmap (pTr 3) ptr).
    napply O_inverts_conn_map.
    exact (isconnmap_pred' 4 _).
  Defined.

  (** The canonical equivalence between the 4- and 3-truncations. *)
  Local Definition pequiv_ptr4_ptr3_psusp_em
    : pTr 4 (psusp K(B, 2)) <~>* K(B, 3)
    := pequiv_ptr3_ptr4_psusp_em^-1* o*E pequiv_ptr (n:=3).

  (** The comparison map collapses the two truncation units of
      [psusp K(B,2)], by naturality of [ptr]. *)
  Local Definition tau_ptr4_ptr3_psusp_em
    : pequiv_ptr4_ptr3_psusp_em o* ptr ==* ptr.
  Proof.
    refine (pmap_prewhisker ptr (compose_cate_fun (A:=pType) _ _) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (ptr_natural 3 ptr)^* @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker ptr (peissect pequiv_ptr3_ptr4_psusp_em) @* _).
    apply pmap_postcompose_idmap.
  Defined.

  (** Pointed maps [K(B,3) ->* K(A,4)] are equivalent to pointed maps
      [K(B,2) ->* K(A,3)], by looping. *)
  Definition equiv_deloop_em_pmap
    : (K(B, 3) ->* K(A, 4)) <~> (K(B, 2) ->* K(A, 3))
    := pequiv_pequiv_postcompose (pequiv_loops_em_em A 3)^-1*
       oE loop_susp_adjoint K(B, 2) K(A, 4)
       oE pequiv_ptr_rec
       oE pequiv_pequiv_precompose pequiv_ptr4_ptr3_psusp_em.

  (** The delooping equivalence, unfolded: postcompose by the inverse loop
      identification, loop the map, precompose by the loop identification. *)
  Definition equiv_deloop_em_pmap_unfold (psi : K(B, 3) ->* K(A, 4))
    : equiv_deloop_em_pmap psi
      ==* (pequiv_loops_em_em A 3)^-1*
          o* (fmap loops psi o* pequiv_loops_em_em B 2).
  Proof.
    transitivity ((pequiv_loops_em_em A 3)^-1*
              o* (fmap loops (psi o* pequiv_ptr4_ptr3_psusp_em o* ptr)
                  o* loop_susp_unit K(B, 2))).
    1: reflexivity.
    symmetry.
    napply pmap_postwhisker.
    refine (pmap_postwhisker _ (loops_em_em_ptr_unit B 1) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ (fmap_comp loops _ _)^* @* _).
    napply pmap_prewhisker.
    tapply (fmap2 loops).
    exact (pmap_compose_assoc psi _ ptr
           @* pmap_postwhisker psi tau_ptr4_ptr3_psusp_em)^*.
  Defined.

End Deloop.

(** Pointed maps from an Eilenberg-Mac Lane space to a connected truncated
    type of the same level which agree on homotopy groups are equal. *)
Definition path_em_pmap_pi_connected `{Univalence} {G : AbGroup@{u}}
  (n : nat) {Y : pType} `{IsConnected n.+1 Y} `{IsTrunc n.+2 Y}
  (phi psi : K(G, n.+2) ->* Y)
  (h : fmap (Pi n.+2) phi == fmap (Pi n.+2) psi)
  : phi = psi.
Proof.
  apply (equiv_inj (pequiv_pequiv_postcompose
    (pequiv_em_connected_truncated Y n.+1)^-1*)).
  napply (path_em_pmap_pi (G' := Build_AbGroup (Pi n.+2 Y) _)).
  intro x.
  refine (fmap_comp (Pi n.+2) phi
    ((pequiv_em_connected_truncated Y n.+1)^-1* : _ ->* _) x @ _).
  refine (ap _ (h x) @ _).
  exact (fmap_comp (Pi n.+2) psi
    ((pequiv_em_connected_truncated Y n.+1)^-1* : _ ->* _) x)^%path.
  Unshelve.
  all: exact _.
Defined.
