From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core Universe Equiv PointedCat Yoneda.
Require Import Pointed.
Require Import Spaces.Nat.Core.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import Homotopy.Suspension.
Require Import Homotopy.ClassifyingSpace.Core.
Import ClassifyingSpaceNotation.
Require Import Homotopy.HSpace.Coherent.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.Hopf.
Require Import Modalities.Descent.
Require Import Truncations.Core Truncations.Connectedness Truncations.SeparatedTrunc.

(** * Eilenberg-Mac Lane spaces *)

Local Open Scope pointed_scope.
Local Open Scope nat_scope.
Local Open Scope mc_mult_scope.

(** ** Maps from connected types to pointed types *)

(** Before specializing to Eilenberg-Mac Lane spaces, we show that when [X] is [n]-connected and [Y] is [n.+1]-truncated, [fmap (Pi n.+1)] is an equivalence.  The case [n=1] is [isequiv_fmap_pi1_pmap], and the inductive step follows from [isequiv_fmap_loops_pmap]. *)

(** Part of the inductive step is factored out here. *)
Local Definition isequiv_fmap_pi_pmap_succ `{Univalence} (n : nat) {X Y : pType}
  (el : IsEquiv (fmap loops (a:=X) (b:=Y)))
  (e : IsEquiv (fmap (Pi n.+1) (a:=loops X) (b:=loops Y)))
  : IsEquiv (fmap (Pi n.+2) (a:=X) (b:=Y)).
Proof.
  pose (a := groupiso_pi_loops n X).
  pose (b := groupiso_pi_loops n Y).
  pose (k := equiv_precompose_cat_equiv a
              oE equiv_postcompose_cat_equiv (x:=Pi n.+1 (loops X)) b^-1$).
  refine (isequiv_homotopic (k o fmap (Pi n.+1) o fmap loops (a:=X) (b:=Y)) _).
  intro f.
  rapply equiv_path_grouphomomorphism.
  intro x.
  exact (moveR_equiv_V (f:=b) _ _ (fmap_pi_loops n.+1 f x)^).
Defined.

(** For [X] [n]-connected and [Y] [n.+1]-truncated, [fmap (Pi n.+1)] is an equivalence from the pointed maps [X ->* Y] to the group homomorphisms [Pi n.+1 X $-> Pi n.+1 Y].  Neither connectivity of [Y] nor truncatedness of [X] is needed.  The induction is on [n]: the successor step is [isequiv_fmap_loops_pmap], which applies since [n.+2 <= n +2+ n], and the base case is [isequiv_fmap_pi1_pmap]. *)
Instance isequiv_fmap_pi_pmap `{Univalence} (n : nat) (X Y : pType)
  `{cX : IsConnected n X} `{tY : IsTrunc n.+1 Y}
  : IsEquiv (fmap (Pi n.+1) (a:=X) (b:=Y)).
Proof.
  induction n in X, Y, cX, tY |- *.
  1: exact (isequiv_fmap_pi1_pmap X Y).
  napply isequiv_fmap_pi_pmap_succ.
  - napply (isequiv_fmap_loops_pmap (n:=n)).
    + exact _.
    + apply (istrunc_leq (trunc_index_leq_add_nat n n)).
  - rapply IHn.
Defined.

Definition equiv_fmap_pi_pmap `{Univalence} (n : nat) (X Y : pType)
  `{IsConnected n X} `{IsTrunc n.+1 Y}
  : (X ->* Y) <~> (Pi n.+1 X $-> Pi n.+1 Y)
  := Build_Equiv _ _ _ (isequiv_fmap_pi_pmap n X Y).

(** Pointed maps from an [n]-connected type to an [n.+1]-truncated type which agree on [Pi n.+1] are equal. *)
Definition path_pmap_pi_connected `{Univalence} (n : nat) {X Y : pType}
  `{IsConnected n X} `{IsTrunc n.+1 Y}
  (phi psi : X ->* Y)
  (h : fmap (Pi n.+1) phi == fmap (Pi n.+1) psi)
  : phi = psi.
Proof.
  tapply (equiv_inj (fmap (Pi n.+1) (a:=X) (b:=Y))).
  exact (equiv_path_grouphomomorphism h).
Defined.

(** Two [n]-connected [n.+1]-truncated pointed types with isomorphic [Pi n.+1] are pointed equivalent. *)
Definition pequiv_pi_connected_truncated `{Univalence} (n : nat) {X Y : pType}
  `{IsConnected n X} `{IsTrunc n.+1 X} `{IsConnected n Y} `{IsTrunc n.+1 Y}
  (phi : GroupIsomorphism (Pi n.+1 X) (Pi n.+1 Y))
  : X <~>* Y
  := cate_reflect_fmap (Pi n.+1) (x:=X) (y:=Y) phi.

(** The equivalence induces the given isomorphism on [Pi n.+1]. *)
Definition fmap_pi_pequiv_pi_connected_truncated `{Univalence} (n : nat) {X Y : pType}
  `{IsConnected n X} `{IsTrunc n.+1 X} `{IsConnected n Y} `{IsTrunc n.+1 Y}
  (phi : GroupIsomorphism (Pi n.+1 X) (Pi n.+1 Y))
  : fmap (Pi n.+1) (pequiv_pi_connected_truncated n phi) == phi
  := fmap_cate_reflect_fmap (Pi n.+1) (x:=X) (y:=Y) phi.

(** ** Definition and properties of Eilenberg-Mac Lane spaces *)

(** The definition of the Eilenberg-Mac Lane spaces.  Note that while we allow [G] to be non-abelian for [n > 1], later results will need to assume that [G] is abelian. *)
Fixpoint EilenbergMacLane@{u v | u <= v} (G : Group@{u}) (n : nat) : pType@{v}
  := match n with
      | 0    => G
      | 1    => pClassifyingSpace@{u} G
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

  (** [K(-, n)] as a functor from groups to pointed types.  [fmap B] and the WildCat functoriality of [psusp] and [pTr] constrain the two groups to a single universe. *)
  Definition K' (n : nat) (G : Group) : pType := K(G, n).

  #[export] Instance is0functor_em (n : nat) : Is0Functor (K' n).
  Proof.
    napply Build_Is0Functor.
    intros G G' f.
    induction n as [|n IHn].
    - exact f.
    - destruct n as [|m].
      + exact (fmap B f).
      + exact (fmap (pTr m.+2) (fmap psusp IHn)).
  Defined.

  #[export] Instance is1functor_em (n : nat) : Is1Functor (K' n).
  Proof.
    napply Build_Is1Functor.
    - intros G G' f g p.
      exact (phomotopy_path (ap (fmap (K' n))
                               (equiv_path_grouphomomorphism p))).
    - intros G.
      induction n as [|[|m] IH].
      + rapply phomotopy_homotopy_hset.
        reflexivity.
      + exact (fmap_id B G).
      + change (fmap (pTr m.+2) (fmap psusp (fmap (K' m.+1) (Id G))) ==* Id (K' m.+2 G)).
        refine (_ @* fmap_id (pTr m.+2) _).
        tapply (fmap2 (pTr m.+2)).
        refine (_ @* fmap_id psusp _).
        tapply (fmap2 psusp).
        exact IH.
    - intros G G' G'' f g.
      induction n as [|[|m] IH].
      + rapply phomotopy_homotopy_hset.
        reflexivity.
      + exact (fmap_comp B f g).
      + change (fmap (K' m.+2) ?f) with (fmap (pTr m.+2) (fmap psusp (fmap (K' m.+1) f))).
        refine (_ @* fmap_comp (pTr m.+2) _ _).
        tapply (fmap2 (pTr m.+2)).
        refine (_ @* fmap_comp psusp _ _).
        tapply (fmap2 psusp).
        exact IH.
  Defined.

  (** TODO: Many results in this file, such as [pi_em_fmap] and [em_fmap_loops_natural], have a large number of universe variables.  These can be reduced by ending various definitions with Qed, but it would be better to fix the source of the explosion of universe variables. *)

  (** At positive levels, [pequiv_loops_em_em] is the canonical comparison map: the loop-suspension unit followed by [loops] of the truncation map.  This presentation makes its naturality transparent, without reference to the Hopf-construction input used to show that it is an equivalence. *)
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

  (** [fmap (K' n)] commutes with the loop-space identifications, so it is a map of spectra. *)
  Definition em_fmap_loops_natural {G G' : AbGroup}
    (f : GroupHomomorphism G G') (n : nat)
    : fmap loops (fmap (K' n.+1) f) o* pequiv_loops_em_em G n
      ==* pequiv_loops_em_em G' n o* fmap (K' n) f.
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

  (** [equiv_g_pi_n_em] at level [n.+1] unfolds to the level-[n] map conjugated by [groupiso_pi_loops] and [pequiv_loops_em_em]. *)
  Local Definition equiv_g_pi_n_em_succ (G : AbGroup) (n : nat) (x : G)
    : equiv_g_pi_n_em G n.+1 x
      = grp_iso_inverse (groupiso_pi_loops _ _)
          (groupiso_pi_functor _ (pequiv_loops_em_em G n.+1)
            (equiv_g_pi_n_em G n x))
    := idpath.

  (** The action of [fmap (K' n.+1) f] on [Pi n.+1] agrees with [f] under the identifications [equiv_g_pi_n_em]. *)
  Definition pi_em_fmap {G G' : AbGroup}
    (f : GroupHomomorphism G G') (n : nat)
    : fmap (Pi n.+1) (fmap (K' n.+1) f) o equiv_g_pi_n_em G n
      == equiv_g_pi_n_em G' n o f.
  Proof.
    induction n as [|n IHn]; intro g.
    - exact (ap tr (bloop_natural G G' f g)).
    - lhs napply (ap _ (equiv_g_pi_n_em_succ G n g)).
      rhs napply (equiv_g_pi_n_em_succ G' n (f g)).
      apply (equiv_inj (groupiso_pi_loops n _)).
      rhs napply (eisretr (groupiso_pi_loops n _) _).
      lhs refine (fmap_pi_loops n.+1 (fmap (K' n.+2) f) _).
      lhs napply (ap _ (eisretr (groupiso_pi_loops n _) _)).
      lhs_V exact (fmap_comp (pPi n.+1)
          (pequiv_loops_em_em G n.+1 : _ ->* _)
          (fmap loops (fmap (K' n.+2) f)) (equiv_g_pi_n_em G n g)).
      lhs exact (fmap2 (pPi n.+1) (em_fmap_loops_natural f n.+1)
          (equiv_g_pi_n_em G n g)).
      lhs exact (fmap_comp (pPi n.+1)
          (fmap (K' n.+1) f) (pequiv_loops_em_em G' n.+1 : _ ->* _)
          (equiv_g_pi_n_em G n g)).
      exact (ap _ (IHn g)).
  Defined.

  (** Equivalently, the composite is conjugation by the identifications [equiv_g_pi_n_em]. *)
  Definition pi_em_fmap' {G G' : AbGroup}
    (f : GroupHomomorphism G G') (n : nat)
    : fmap (Pi n.+1) (fmap (K' n.+1) f)
      == equiv_g_pi_n_em G' n o f o (equiv_g_pi_n_em G n)^-1
    := cate_moveL_eV (A:=Group) _ _ (equiv_g_pi_n_em G' n $o f) (pi_em_fmap f n).

  (** Eilenberg-Mac Lane spaces of a contractible group are contractible. *)
  #[export] Instance contr_em_contr {G : Group} `{Contr G} (n : nat)
    : Contr K(G, n).
  Proof.
    induction n as [|[|n] IHn].
    - exact _.
    - exact _.
    - rapply contr_O_contr.
  Defined.

  (** [K(-,n)] is a pointed functor. *)
  #[export] Instance ispointedfunctor_em (n : nat)
    : IsPointedFunctor (K' n).
  Proof.
    rapply Build_IsPointedFunctor'; cbn.
    snapply Build_pEquiv.
    1: exact pconst.
    rapply isequiv_contr_contr.
  Defined.

  (** [fmap (K' n.+1) f] of a surjective homomorphism is an [n]-connected map.  Both surjectivity of the map and of its [ap]s reduce to the previous level through the loop-space identifications. *)
  #[export] Instance isconnmap_em_fmap {G G' : AbGroup}
    (f : GroupHomomorphism G G') `{!IsSurjection f} (n : nat)
    : IsConnMap n (fmap (K' n.+1) f).
  Proof.
    induction n as [|n IHn].
    - exact (isconnmap_fmap_pclassifyingspace f).
    - snapply isconnmap_isconnmap_ap_surj.
      + rapply (isconnmap_isconnected (-1)).
      + assert (c : IsConnMap n (fmap loops (fmap (K' n.+2) f))).
        { refine (conn_map_homotopic _
            ((pequiv_loops_em_em G' n.+1 o* fmap (K' n.+1) f)
             o* (pequiv_loops_em_em G n.+1)^-1*) _
            (fun p =>
              (moveL_pequiv_fV _ _ _ (em_fmap_loops_natural f n.+1))^* p) _). }
        rapply (conn_point_elim (-1) (A:=K(G, n.+2))).
        rapply (conn_point_elim (-1) (A:=K(G, n.+2))).
        intro q.
        pose (e2 := equiv_concat_l (point_eq (fmap (K' n.+2) f))^ _
                    oE equiv_concat_r (point_eq (fmap (K' n.+2) f)) _).
        exact (isconnected_equiv' n _
                 (equiv_functor_sigma_id (fun p => equiv_ap e2 _ _))^-1%equiv
                 (c _)).
  Defined.

  (** [fmap (K' n.+1)] is an equivalence from group homomorphisms to pointed maps.  Since [K(G, n.+1)] is [n]-connected and [K(G', n.+1)] is [n.+1]-truncated, [fmap (Pi n.+1)] is an equivalence from the pointed maps to the group homomorphisms [Pi n.+1 K(G, n.+1) $-> Pi n.+1 K(G', n.+1)], and by [pi_em_fmap'] the composite with [fmap (K' n.+1)] is conjugation by the identifications [equiv_g_pi_n_em], which is also an equivalence.  In particular, pointed maps between Eilenberg-Mac Lane spaces of the same level are determined by their effect on homotopy groups. *)
  #[export] Instance isequiv_em_fmap (G G' : AbGroup) (n : nat)
    : IsEquiv (fun f : GroupHomomorphism G G' => fmap (K' n.+1) f).
  Proof.
    refine (isequiv_commsq' _
              (equiv_precompose_cat_equiv (A:=Group)
                 (grp_iso_inverse (equiv_g_pi_n_em G n)))
              (equiv_postcompose_cat_equiv (A:=Group) (equiv_g_pi_n_em G' n))
              (fmap (Pi n.+1)) _).
    intro f.
    apply equiv_path_grouphomomorphism; symmetry.
    apply pi_em_fmap'.
  Defined.

  (** The equivalence between group homomorphisms and pointed maps of Eilenberg-Mac Lane spaces. *)
  Definition equiv_em_fmap (G G' : AbGroup) (n : nat)
    : GroupHomomorphism G G' <~> (K(G, n.+1) ->* K(G', n.+1))
    := Build_Equiv _ _ _ (isequiv_em_fmap G G' n).

  (** The canonical identification of [Pi n.+1 K(Pi n.+1 X, n.+1)] with [Pi n.+1 X].  For [n = 0] this is [grp_iso_g_pi1_bg], and for positive [n] it is [equiv_g_pi_n_em] applied to the abelian group [Pi n.+1 X]. *)
  Definition grp_iso_pi_em_pi (X : pType) (n : nat)
    : GroupIsomorphism (Pi n.+1 K(Pi n.+1 X, n.+1)) (Pi n.+1 X).
  Proof.
    symmetry.
    destruct n as [|m].
    - exact grp_iso_g_pi1_bg.
    - exact (equiv_g_pi_n_em (Build_AbGroup (Pi m.+2 X) _) m.+1).
  Defined.

  (** Every pointed (n-1)-connected n-type is an Eilenberg-Mac Lane space. *)
  Definition pequiv_em_connected_truncated (X : pType)
    (n : nat) `{IsConnected n X} `{IsTrunc n.+1 X}
    : K(Pi n.+1 X, n.+1) <~>* X
    := pequiv_pi_connected_truncated n (grp_iso_pi_em_pi X n).

  (** It induces [grp_iso_pi_em_pi] on [Pi n.+1]. *)
  Definition fmap_pi_pequiv_em_connected_truncated (X : pType)
    (n : nat) `{IsConnected n X} `{IsTrunc n.+1 X}
    : fmap (Pi n.+1) (pequiv_em_connected_truncated X n) == grp_iso_pi_em_pi X n
    := fmap_pi_pequiv_pi_connected_truncated n (grp_iso_pi_em_pi X n).

End EilenbergMacLane.

(** ** Delooping Eilenberg-Mac Lane mapping types *)

Section Deloop.
  Context `{Univalence} (B A : AbGroup@{u}) (n : nat).

  (** [Pi n.+4 (psusp K(B,n.+2))] is trivial. *)
  Local Instance contr_pi_psusp_em : Contr (Pi n.+4 (psusp K(B, n.+2))).
  Proof.
    nrefine (contr_equiv' (Pi n.+3 (loops (psusp K(B, n.+2)))) _).
    1: exact (groupiso_pi_loops n.+2 (psusp K(B, n.+2)))^-1%equiv.
    (* Since [Pi n.+3] is a set, it's enough to show it's 0-connected. *)
    napply (contr_trunc_conn 0); only 1: exact _.
    (* And for that, it's enough to show it's the target of a (-1)-connected map from a 0-connected type. *)
    pose (fu := fmap (pPi n.+3) (loop_susp_unit K(B, n.+2))).
    napply (OO_isconnected_from_conn_map 0 (Tr (-1)) fu).
    1, 2: exact _.
    - napply isconnected_contr.
      rapply contr_pi_istrunc.
    - apply (issurj_pi_connmap n.+2).
      napply (isconnmap_pred_add n.-2).
      rewrite 2 trunc_index_add_succ.
      exact (conn_map_loop_susp_unit n K(B, n.+2)).
  Defined.

  (** [pTr n.+4 (psusp K(B,n.+2))] is [n.+3]-truncated. *)
  Local Instance istrunc_ptr_psusp_em
    : IsTrunc n.+3 (pTr n.+4 (psusp K(B, n.+2))).
  Proof.
    napply (istrunc_contr_pi n.+3).
    1,2: exact _.
    exact (contr_equiv' _ (grp_iso_pi_Tr n.+3 (psusp K(B, n.+2)))).
  Defined.

  (** [K(B, n.+3)] is the [n.+3]-truncation of [pTr n.+4 (psusp K(B, n.+2))]. *)
  Local Definition pequiv_ptr_ptr_psusp_em
    : K(B, n.+3) <~>* pTr n.+3 (pTr n.+4 (psusp K(B, n.+2))).
  Proof.
    snapply Build_pEquiv'.
    - rapply equiv_O_functor_to_O_O_leq.
    - reflexivity.
  Defined.

  (** The canonical equivalence between the [n.+4]- and [n.+3]-truncations. *)
  Local Definition pequiv_ptr_psusp_em
    : pTr n.+4 (psusp K(B, n.+2)) <~>* K(B, n.+3)
    := pequiv_ptr_ptr_psusp_em^-1* o*E pequiv_ptr.

  (** [pequiv_ptr_psusp_em] commutes with the truncation unit [ptr]. *)
  Local Definition tau_ptr_psusp_em
    : pequiv_ptr_psusp_em o* ptr ==* ptr.
  Proof.
    unfold pequiv_ptr_psusp_em.
    lhs' napply pmap_compose_assoc.
    rapply (cate_moveR_Ve (H0:=hasequivs_ptype)).
    apply ptr_natural.
  Qed.

  (** Pointed maps [K(B,n.+3) ->* K(A,n.+4)] are equivalent to pointed maps [K(B,n.+2) ->* K(A,n.+3)].  This is an instance of the stabilization theorem, Buchholtz-van Doorn-Rijke, Theorem 6.7; as there, it follows from the truncated suspension-loops adjunction, with the Freudenthal input carried by [pequiv_loops_em_em]. *)
  Definition equiv_deloop_em_pmap
    : (K(B, n.+3) ->* K(A, n.+4)) <~> (K(B, n.+2) ->* K(A, n.+3))
    := pequiv_pequiv_postcompose (pequiv_loops_em_em A n.+3)^-1*
       oE loop_susp_adjoint K(B, n.+2) K(A, n.+4)
       oE pequiv_ptr_rec
       oE pequiv_pequiv_precompose pequiv_ptr_psusp_em.

  (** [equiv_deloop_em_pmap] as looping conjugated by the loop identifications. *)
  Definition equiv_deloop_em_pmap_unfold (psi : K(B, n.+3) ->* K(A, n.+4))
    : equiv_deloop_em_pmap psi
      ==* (pequiv_loops_em_em A n.+3)^-1*
          o* (fmap loops psi o* pequiv_loops_em_em B n.+2).
  Proof.
    change (equiv_deloop_em_pmap psi) with
      ((pequiv_loops_em_em A n.+3)^-1*
         o* (fmap loops (psi o* pequiv_ptr_psusp_em o* ptr)
               o* loop_susp_unit K(B, n.+2))).
    napply pmap_postwhisker.
    rhs' napply (pmap_postwhisker _ (loops_em_em_ptr_unit B n.+1)).
    rhs_V' napply pmap_compose_assoc.
    refine (pmap_prewhisker _ (_ @* fmap_comp loops _ _)).
    tapply (fmap2 loops).
    exact (pmap_compose_assoc psi _ ptr
           @* pmap_postwhisker psi tau_ptr_psusp_em).
  Qed.

End Deloop.
