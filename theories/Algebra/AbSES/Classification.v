From HoTT Require Import Basics Types Truncations.Core
  Truncations.Connectedness Truncations.SeparatedTrunc.
From HoTT.WildCat Require Import Core Equiv PointedCat.
Require Import Pointed.
Require Import AbelianGroup.
Require Import Algebra.AbSES.Core Algebra.AbSES.Ext.
Require Import Universes.Smallness.
Require Import Homotopy.HomotopyGroup Homotopy.EMSpace Homotopy.ExactSequence.
Require Import Homotopy.WhiteheadsPrinciple.
Require Import Groups.Group Groups.ShortExactSequence.
Require Import HSet.
Require Import Modalities.Identity Modalities.Descent.

(** * Classification of short exact sequences

Short exact sequences [A -> E -> B] of abelian groups are classified by pointed maps [K(B,2) ->* K(A,3)] (Christensen and Flaten, "Ext groups in homotopy type theory", Theorem 2.2.2). *)

Local Open Scope pointed_scope.

(** TODO: The main results of this file, such as [equiv_abses_classifying_map] and [issmall_abses], have a large number of universe variables, inherited from the delooping layer in EMSpace.v.  See the TODO there. *)

(** [K(-, n)] is a pointed functor, so it takes the complex underlying a short exact sequence to a complex. *)
Definition iscomplex_em_abses `{Univalence} {B A : AbGroup@{u}} (E : AbSES B A)
  (n : nat)
  : IsComplex (fmap (K' n) (inclusion E)) (fmap (K' n) (projection E))
  := fmap_iscomplex (K' n) _ _ (iscomplex_abses E).

Section EMFiberSequence.
  Context `{Univalence} {B A : AbGroup@{u}} (E : AbSES B A) (n : nat).

  (** The identifications [equiv_g_pi_n_em] carry [Pi n.+1] of the sequence [K(-, n.+1)] applied to [E] back to [E] itself, so that sequence is exact. *)
  Local Definition isexact_pi_em_abses
    : IsExact (Tr (-1))
        (fmap (Pi n.+1) (fmap (K' n.+1) (inclusion E)))
        (fmap (Pi n.+1) (fmap (K' n.+1) (projection E))).
  Proof.
    napply (isexact_square_if _ (i := inclusion E) (f := projection E)
      (grp_iso_inverse (equiv_g_pi_n_em A n))
      (grp_iso_inverse (equiv_g_pi_n_em E n))
      (grp_iso_inverse (equiv_g_pi_n_em B n))).
    - srapply phomotopy_homotopy_hset; intro x.
      refine (ap (grp_iso_inverse (equiv_g_pi_n_em E n))
        (ap (fmap (Pi n.+1) (fmap (K' n.+1) (inclusion E)))
           (eisretr (equiv_g_pi_n_em A n) x)^
         @ pi_em_fmap (inclusion E) n _) @ _).
      exact (eissect (equiv_g_pi_n_em E n) _).
    - srapply phomotopy_homotopy_hset; intro x.
      refine (ap (grp_iso_inverse (equiv_g_pi_n_em B n))
        (ap (fmap (Pi n.+1) (fmap (K' n.+1) (projection E)))
           (eisretr (equiv_g_pi_n_em E n) x)^
         @ pi_em_fmap (projection E) n _) @ _).
      exact (eissect (equiv_g_pi_n_em B n) _).
    - exact _.
  Defined.

  (** The fiber inclusion of [K(-, n.+1)] of the projection is an embedding on [Pi n.+1], since the homotopy group mapping into it vanishes. *)
  Local Definition isembedding_pi_pfib_em
    : IsEmbedding
        (fmap (pPi n.+1) (pfib (fmap (K' n.+1) (projection E)))).
  Proof.
    napply (isembedding_isexact (A := pPi n.+2 K(B, n.+1))).
    1: exact (contr_pi_succ_istrunc n.+1 K(B, n.+1)).
    exact (isexact_pi_fiber _ _ n.+1).
  Defined.

  (** Both [Pi n.+1 K(A, n.+1)] and [Pi n.+1] of the fiber are the kernel of [Pi n.+1] of the projection, so the comparison map identifies them. *)
  Local Instance isequiv_pi_cxfib
    : IsEquiv (fmap (Pi n.+1) (cxfib (iscomplex_em_abses E n.+1))).
  Proof.
    napply isequiv_isexact_factor.
    - intro x.
      exact ((fmap_comp (Pi n.+1) (cxfib (iscomplex_em_abses E n.+1))
                (pfib (fmap (K' n.+1) (projection E))) x)^
             @ fmap2 (Pi n.+1) (pfib_cxfib _) x).
    - (* [Pi n.+1] of [K(-, n.+1)] of the inclusion is conjugate to the inclusion. *)
      apply isembedding_isinj_hset.
      intros x y q.
      apply (equiv_inj (equiv_g_pi_n_em A n)^-1%equiv).
      rapply (isinj_embedding (inclusion E)).
      apply (equiv_inj (equiv_g_pi_n_em E n)).
      lhs_V napply (pi_em_fmap (inclusion E) n _).
      rhs_V napply (pi_em_fmap (inclusion E) n _).
      exact (ap _ (eisretr (equiv_g_pi_n_em A n) x) @ q
             @ ap _ (eisretr (equiv_g_pi_n_em A n) y)^).
    - exact isembedding_pi_pfib_em.
    - exact isexact_pi_em_abses.
    - exact (cx_isexact (IsExact := isexact_pi_total _ _ n.+1)).
  Defined.

  (** Both sides are [n]-connected and [n.+1]-truncated, so the comparison map is an equivalence by Whitehead's principle. *)
  Local Instance isequiv_cxfib_em
    : IsEquiv (cxfib (iscomplex_em_abses E n.+1)).
  Proof.
    pose proof (isconnmap_em_fmap (projection E) n (point _)).
    napply (isequiv_pi_connected_truncated n).
    1,2,3,4: exact _.
    exact isequiv_pi_cxfib.
  Defined.

  (** [K(-, n.+1)] sends short exact sequences of abelian groups to fiber sequences of Eilenberg-Mac Lane spaces. *)
  #[export] Instance isexact_em_abses
    : IsExact purely (fmap (K' n.+1) (inclusion E))
        (fmap (K' n.+1) (projection E)).
  Proof.
    exists (iscomplex_em_abses E n.+1).
    rapply conn_map_isequiv.
  Defined.

End EMFiberSequence.

(** ** The classifying map of a short exact sequence

The connecting map of the fiber sequence [K(A,3) -> K(E,3) -> K(B,3)], expressed as a pointed map [K(B,2) ->* K(A,3)]. *)
Definition abses_classifying_map `{Univalence} {B A : AbGroup@{u}}
  (E : AbSES B A)
  : K(B, 2) ->* K(A, 3)
  := connecting_map (fmap (K' 3) (inclusion E)) (fmap (K' 3) (projection E))
     o* pequiv_loops_em_em B 2.

(** ** The short exact sequence of a pointed map

Conversely, a pointed map [f : K(B,2) ->* K(A,3)] yields a short exact sequence [A -> Pi 2 (pfiber f) -> B], by rotating the fiber sequence of [f] and taking homotopy groups. *)

Section AbSESPfiber.
  Context `{Univalence} {B A : AbGroup@{u}} (n : nat)
    (f : K(B, n.+2) ->* K(A, n.+3)).

  (** The middle group: [Pi n.+2] of the fiber, abelian by Eckmann-Hilton. *)
  Definition abgroup_pi_pfiber : AbGroup
    := Build_AbGroup (Pi n.+2 (pfiber f)) _.

  (** [A] is the [n.+2]-nd homotopy group of [loops K(A, n.+3)]. *)
  Local Definition grp_iso_a_pi_loops
    : GroupIsomorphism A (Pi n.+2 (loops K(A, n.+3)))
    := grp_iso_compose (groupiso_pi_loops n.+1 K(A, n.+3))
         (equiv_g_pi_n_em A n.+2).

  (** The inclusion, through the rotated fiber sequence [loops K(A,n+3) -> pfiber f -> K(B,n+2)]. *)
  Definition abses_pfiber_incl : A $-> abgroup_pi_pfiber
    := grp_homo_compose (fmap (Pi n.+2) (connecting_map (pfib f) f))
         grp_iso_a_pi_loops.

  (** The projection, induced by the fiber inclusion of [f]. *)
  Definition abses_pfiber_proj : abgroup_pi_pfiber $-> B
    := grp_homo_compose (grp_iso_inverse (equiv_g_pi_n_em B n.+1))
         (fmap (Pi n.+2) (pfib f)).

  (** The two homotopy groups neighbouring the sequence vanish. *)
  Local Instance contr_pi_em : Contr (Pi n.+2 K(A, n.+3))
    := contr_pi_isconnected n.+2 K(A, n.+3).

  Local Instance contr_pi_em' : Contr (Pi n.+3 K(B, n.+2))
    := contr_pi_succ_istrunc n.+2 K(B, n.+2).

  (** The three conditions defining a short exact sequence therefore come from the long exact sequences of the fiber sequence of [f] and of its rotation. *)

  Local Instance isembedding_abses_pfiber_incl : IsEmbedding abses_pfiber_incl.
  Proof.
    assert (emb : IsEmbedding (fmap (pPi n.+2) (connecting_map (pfib f) f))).
    { napply (isembedding_isexact (A := pPi n.+3 K(B, n.+2))).
      1: exact _.
      exact (isexact_pi_fiber (connecting_map (pfib f) f) (pfib f) n.+2). }
    apply isembedding_isinj_hset.
    intros x y q.
    apply (equiv_inj grp_iso_a_pi_loops).
    exact (isinj_embedding _ emb _ _ q).
  Defined.

  Local Definition issurjection_abses_pfiber_proj
    : IsSurjection abses_pfiber_proj.
  Proof.
    pose proof (isexact_pi_total (pfib f) f n.+2) as ex.
    assert (surj : IsConnMap (Tr (-1)) (fmap (pPi n.+2) (pfib f)))
      by exact (@isconnmap_O_isexact_base_contr (Tr (-1)) _ _ _ _
                  (fmap (pPi n.+2) (pfib f)) (fmap (pPi n.+2) f) ex).
    exact (conn_map_compose _ (fmap (pPi n.+2) (pfib f))
             (grp_iso_inverse (equiv_g_pi_n_em B n.+1))).
  Defined.

  Local Instance isexact_abses_pfiber
    : IsExact (Tr (-1)) abses_pfiber_incl abses_pfiber_proj.
  Proof.
    assert (ex : IsExact (Tr (-1))
                   (fmap (Pi n.+2) (connecting_map (pfib f) f))
                   (fmap (Pi n.+2) (pfib f)))
      by exact (isexact_pi_total (connecting_map (pfib f) f) (pfib f) n.+2).
    napply (isexact_square_if _
      grp_iso_a_pi_loops pequiv_pmap_idmap (equiv_g_pi_n_em B n.+1)).
    3: exact ex.
    1: srapply phomotopy_homotopy_hset; intro x; reflexivity.
    srapply phomotopy_homotopy_hset; intro x.
    exact (eisretr (equiv_g_pi_n_em B n.+1) _).
  Defined.

  (** The short exact sequence associated to [f]. *)
  Definition abses_pfiber : AbSES B A
    := Build_AbSES abgroup_pi_pfiber abses_pfiber_incl abses_pfiber_proj
         _ issurjection_abses_pfiber_proj _.

End AbSESPfiber.

Section PfiberDeloop.
  Context `{Univalence} {B A : AbGroup@{u}} (psi : K(B, 3) ->* K(A, 4)).

  (** The second homotopy group of the fiber is trivial, since it embeds into the trivial [Pi 2 K(B,3)]. *)
  Local Instance contr_pi2_pfiber_em : Contr (Pi 2 (pfiber psi)).
  Proof.
    assert (emb : IsEmbedding (fmap (pPi 2) (pfib psi))).
    { napply (isembedding_isexact (A := pPi 3 K(A, 4))).
      1: exact (contr_pi_isconnected 3 K(A, 4)).
      exact (isexact_pi_fiber _ _ 2). }
    apply (Build_Contr _ mon_unit).
    intro y.
    napply (isinj_embedding _ emb).
    napply path_contr.
    exact (contr_pi_isconnected 2 K(B, 3)).
  Defined.

  (** The fiber is 2-connected. *)
  Local Instance isconnected_pfiber_em : IsConnected 2 (pfiber psi).
  Proof.
    napply (isconnected_succ_contr_pi 0).
    - pose @O_lex_leq_Tr.
      pose proof (@isconnected_pred 2 K(A, 4) (isconnected_em 3)).
      pose proof (isconnected_em (G:=B) 2).
      rapply OO_isconnected_hfiber.
    - exact _.
  Defined.

  (** The fiber is the Eilenberg-Mac Lane space of its third homotopy group. *)
  Local Definition pequiv_em_pfiber_psi
    : K(abgroup_pi_pfiber 1 psi, 3) <~>* pfiber psi
    := pequiv_em_connected_truncated (pfiber psi) 2.

  (** The induced identification of third homotopy groups. *)
  Local Definition eta_pfiber_psi
    : GroupIsomorphism (abgroup_pi_pfiber 1 psi) (abgroup_pi_pfiber 1 psi)
    := grp_iso_compose
         (groupiso_pi_functor 2 pequiv_em_pfiber_psi)
         (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2).

  (** The bridge, twisted by [eta_pfiber_psi]. *)
  Local Definition pequiv_em_pfiber_psi'
    : K(abgroup_pi_pfiber 1 psi, 3) <~>* pfiber psi.
  Proof.
    snapply Build_pEquiv.
    1: exact (pequiv_em_pfiber_psi
        o* emap (K' 3) (grp_iso_inverse eta_pfiber_psi)).
    exact (isequiv_compose
      (emap (K' 3) (grp_iso_inverse eta_pfiber_psi))
      pequiv_em_pfiber_psi).
  Defined.

  (** On [Pi 3], the bridge inverts [equiv_g_pi_n_em], by construction. *)
  Local Definition pi_bridge_psi (x : Pi 3 K(abgroup_pi_pfiber 1 psi, 3))
    : fmap (Pi 3) (pequiv_em_pfiber_psi') x
      = grp_iso_inverse (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) x.
  Proof.
    refine (fmap_comp (Pi 3)
      (fmap (K' 3) (grp_iso_inverse eta_pfiber_psi))
      (pequiv_em_pfiber_psi) x @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi))
      (ap (fmap (Pi 3) (fmap (K' 3) (grp_iso_inverse eta_pfiber_psi)))
        (eisretr
          (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) x)^) @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi))
      (pi_em_fmap (grp_iso_inverse eta_pfiber_psi) 2 _) @ _).
    exact (eisretr eta_pfiber_psi _).
  Defined.

  (** Through the bridge, [fmap (K' 3)] of the projection is the fiber inclusion of [psi]. *)
  Local Definition path_em_proj_pfib_psi
    : fmap (K' 3) (abses_pfiber_proj 1 psi)
      = pfib psi o* pequiv_em_pfiber_psi'.
  Proof.
    snapply (path_pmap_pi_connected 1).
    1,2: exact _.
    1: exact (isconnected_em (G:=B) 2).
    1: exact _.
    intro x.
    refine (ap (fmap (Pi 3) (fmap (K' 3) (abses_pfiber_proj 1 psi)))
      (eisretr (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) x)^
      @ _).
    refine (pi_em_fmap (abses_pfiber_proj 1 psi) 2 _ @ _).
    refine (eisretr (equiv_g_pi_n_em B 2) _ @ _).
    refine (_ @ (fmap_comp (Pi 3)
      (pequiv_em_pfiber_psi') (pfib psi) x)^).
    exact (ap (fmap (Pi 3) (pfib psi)) (pi_bridge_psi x)^).
  Qed.

  (** Through the bridge, [fmap (K' 3)] of the inclusion is the connecting map of [psi], modulo the loop identification of [K(A,3)]. *)
  Local Definition path_em_incl_delta_psi
    : pequiv_em_pfiber_psi' o* fmap (K' 3) (abses_pfiber_incl 1 psi)
      = connecting_map (pfib psi) psi o* pequiv_loops_em_em A 3.
  Proof.
    snapply (path_pmap_pi_connected 1).
    1,2: exact _.
    1: exact _.
    1: exact _.
    intro x.
    refine (fmap_comp (Pi 3)
      (fmap (K' 3) (abses_pfiber_incl 1 psi))
      (pequiv_em_pfiber_psi') x @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi'))
      (ap (fmap (Pi 3) (fmap (K' 3) (abses_pfiber_incl 1 psi)))
        (eisretr (equiv_g_pi_n_em A 2) x)^) @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi'))
      (pi_em_fmap (abses_pfiber_incl 1 psi) 2 _) @ _).
    refine (pi_bridge_psi _ @ _).
    refine (eissect
      (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) _ @ _).
    refine (_ @ (fmap_comp (Pi 3)
      (pequiv_loops_em_em A 3)
      (connecting_map (pfib psi) psi) x)^).
    refine (ap (fmap (Pi 3) (connecting_map (pfib psi) psi)) _).
    refine (eisretr (groupiso_pi_loops 2 K(A, 4)) _ @ _).
    exact (ap (fmap (Pi 3) (pequiv_loops_em_em A 3))
      (eisretr (equiv_g_pi_n_em A 2) x)).
  Qed.

  (** The projection square as a square of pointed maps. *)
  Local Definition square_em_proj_pfib_psi
    : pequiv_pmap_idmap o* fmap (K' 3) (projection (abses_pfiber 1 psi))
      ==* pfib psi o* pequiv_em_pfiber_psi'
    := pmap_postcompose_idmap _ @* phomotopy_path path_em_proj_pfib_psi.

  (** [Pi 3] of the fiber inclusion of [pfib psi] is an embedding, since the homotopy group mapping into it vanishes. *)
  Local Definition isembedding_pi_pfib_pfib_psi
    : IsEmbedding (fmap (pPi 3) (pfib (pfib psi))).
  Proof.
    napply (isembedding_isexact (A := pPi 4 K(B, 3))).
    1: exact (contr_pi_succ_istrunc 3 K(B, 3)).
    exact (isexact_pi_fiber _ _ 3).
  Defined.

  (** Through the bridge, [cxfib] of the extracted sequence is the connecting identification of [psi], modulo the loop identification of [K(A,3)]. *)
  Local Definition path_cxfib_connect_psi
    : pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
        square_em_proj_pfib_psi
      o* pequiv_cxfib (i := fmap (K' 3) (inclusion (abses_pfiber 1 psi)))
           (f := fmap (K' 3) (projection (abses_pfiber 1 psi)))
      = (connect_fiberseq (pfib psi) psi).2 o* pequiv_loops_em_em A 3.
  Proof.
    snapply (path_pmap_pi_connected 1).
    1,2: exact _.
    1: exact (isconnected_equiv' 2 (loops K(A, 4))
         ((connect_fiberseq (pfib psi) psi).2)
         (@isconnected_loops _ 2 K(A, 4) (isconnected_em 3))).
    1: exact _.
    intro x.
    napply (isinj_embedding _ isembedding_pi_pfib_pfib_psi).
    refine (ap (fmap (Pi 3) (pfib (pfib psi)))
      (fmap_comp (Pi 3)
        (pequiv_cxfib (i := fmap (K' 3) (inclusion (abses_pfiber 1 psi)))
           (f := fmap (K' 3) (projection (abses_pfiber 1 psi))))
        (pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
           square_em_proj_pfib_psi) x) @ _).
    refine ((fmap_comp (Pi 3)
      (pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
         square_em_proj_pfib_psi)
      (pfib (pfib psi)) _)^ @ _).
    refine ((fmap2 (Pi 3)
      (square_pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
         square_em_proj_pfib_psi) _)^ @ _).
    refine (fmap_comp (Pi 3)
      (pfib (fmap (K' 3) (projection (abses_pfiber 1 psi))))
      (pequiv_em_pfiber_psi') _ @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi'))
      ((fmap_comp (Pi 3)
         (pequiv_cxfib (i := fmap (K' 3) (inclusion (abses_pfiber 1 psi)))
            (f := fmap (K' 3) (projection (abses_pfiber 1 psi))))
         (pfib (fmap (K' 3) (projection (abses_pfiber 1 psi)))) x)^
       @ fmap2 (Pi 3) (pfib_cxfib _) x) @ _).
    refine ((fmap_comp (Pi 3)
      (fmap (K' 3) (abses_pfiber_incl 1 psi))
      (pequiv_em_pfiber_psi') x)^ @ _).
    refine (ap (fun m => fmap (Pi 3) m x)
      path_em_incl_delta_psi @ _).
    refine (fmap_comp (Pi 3)
      (pequiv_loops_em_em A 3)
      (connecting_map (pfib psi) psi) x @ _).
    refine (fmap_comp (Pi 3)
      ((connect_fiberseq (pfib psi) psi).2)
      (pfib (pfib psi)) _ @ _).
    exact (ap (fmap (Pi 3) (pfib (pfib psi)))
      (fmap_comp (Pi 3)
        (pequiv_loops_em_em A 3)
        ((connect_fiberseq (pfib psi) psi).2) x))^.
  Qed.

  (** The connecting identification of [psi] inverts [pfiber2_loops], since the underlying [pequiv_pfiber] square is tautological. *)
  Local Definition pfiber2_loops_connect_psi
    : pfiber2_loops psi o* ((connect_fiberseq (pfib psi) psi).2)
      ==* pmap_idmap.
  Proof.
    refine (pmap_prewhisker _ _ @* peisretr
      ((pfiber2_loops psi)
       o*E (pequiv_pfiber _ _ (square_pfib_pequiv_cxfib (pfib psi) psi)))).
    exact (pmap_postwhisker _ (pequiv_pfiber_cxfib_taut psi)
           @* pmap_precompose_idmap _)^*.
  Qed.

  (** Through the loop identification of [K(A,3)], the connecting map of the extracted fiber sequence is [loops psi], twisted by loop inversion. *)
  Local Definition connecting_map_em_loops_psi
    : pequiv_loops_em_em A 3
      o* connecting_map (fmap (K' 3) (inclusion (abses_pfiber 1 psi)))
           (fmap (K' 3) (projection (abses_pfiber 1 psi)))
      ==* fmap loops psi o* loops_inv K(B, 3).
  Proof.
    (* Insert the identity [pfiber2_loops psi o* connect] in front. *)
    refine ((pmap_postcompose_idmap _)^* @* _).
    refine (pmap_prewhisker _ pfiber2_loops_connect_psi^* @* _).
    (* Reassociate to expose the connecting composite, then the cxfib square. *)
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_postwhisker _
      (pmap_prewhisker _ (phomotopy_path path_cxfib_connect_psi^)) @* _).
    (* Compare the connecting maps across the bridge. *)
    refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _) @* _).
    refine (pmap_postwhisker _
      (pmap_postwhisker _ (connecting_map_cxfib _ _)) @* _).
    refine (pmap_postwhisker _
      (connecting_map_natural _ _ square_em_proj_pfib_psi) @* _).
    refine (pmap_postwhisker _
      (pmap_postwhisker _ (fmap_id loops _)
       @* pmap_precompose_idmap _) @* _).
    exact (connecting_map_pfib2 psi).
  Qed.

  (** Negation on [K(B,2)], as loop inversion conjugated by the loop identification. *)
  Local Definition pequiv_neg_em : K(B, 2) <~>* K(B, 2)
    := (pequiv_loops_em_em B 2)^-1*
       o*E (loops_inv K(B, 3) o*E pequiv_loops_em_em B 2).

  (** Under the loop identification, [pequiv_neg_em] is loop inversion. *)
  Local Definition pequiv_neg_em_loops
    : pequiv_loops_em_em B 2 o* pequiv_neg_em
      ==* loops_inv K(B, 3) o* pequiv_loops_em_em B 2.
  Proof.
    lhs_V' napply pmap_compose_assoc.
    lhs' napply (pmap_prewhisker _ (peisretr (pequiv_loops_em_em B 2))).
    napply pmap_postcompose_idmap.
  Qed.

  (** The classifying map of the extracted sequence is the delooping equivalence applied to [psi], twisted by [pequiv_neg_em]. *)
  Local Definition abses_classifying_pfiber_deloop
    : abses_classifying_map (abses_pfiber 1 psi)
      ==* equiv_deloop_em_pmap B A 0 psi o* pequiv_neg_em.
  Proof.
    refine (_ @* (pmap_prewhisker pequiv_neg_em
                    (equiv_deloop_em_pmap_unfold B A 0 psi)
                  @* pmap_compose_assoc _ _ _
                  @* pmap_postwhisker _ (pmap_compose_assoc _ _ _))^*).
    refine (pmap_prewhisker (pequiv_loops_em_em B 2)
              (moveL_pequiv_Vf _ _ _ connecting_map_em_loops_psi) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _) @* _).
    napply pmap_postwhisker.
    napply pmap_postwhisker.
    symmetry; exact pequiv_neg_em_loops.
  Qed.

End PfiberDeloop.

(** ** The first round trip

The short exact sequence extracted from the classifying map of [E] is [E] itself. *)

Section ClassifyingRoundTrip.
  Context `{Univalence} {B A : AbGroup@{u}} (E : AbSES B A).

  (** The classifying map equals the connecting map after the loop identification, as a square. *)
  Local Definition rt1_square
    : pequiv_pmap_idmap o* abses_classifying_map E
      ==* connecting_map (fmap (K' 3) (inclusion E))
            (fmap (K' 3) (projection E))
          o* pequiv_loops_em_em B 2
    := pmap_postcompose_idmap _.

  (** The fiber of the connecting map's defining presentation. *)
  Local Definition rt1_pfiber_delta
    : pfiber (connecting_map (fmap (K' 3) (inclusion E))
                (fmap (K' 3) (projection E)))
      <~>* pfiber (pfib (fmap (K' 3) (inclusion E))).
  Proof.
    refine (pequiv_pfiber
      ((connect_fiberseq (fmap (K' 3) (inclusion E))
          (fmap (K' 3) (projection E))).2)
      pequiv_pmap_idmap _).
    exact (pmap_postcompose_idmap _).
  Defined.

  (** Its defining square. *)
  Local Definition rt1_pfiber_delta_square
    : (connect_fiberseq (fmap (K' 3) (inclusion E))
         (fmap (K' 3) (projection E))).2
      o* pfib (connecting_map (fmap (K' 3) (inclusion E))
                 (fmap (K' 3) (projection E)))
      ==* pfib (pfib (fmap (K' 3) (inclusion E))) o* rt1_pfiber_delta.
  Proof.
    refine (square_pequiv_pfiber
      ((connect_fiberseq (fmap (K' 3) (inclusion E))
          (fmap (K' 3) (projection E))).2)
      pequiv_pmap_idmap _).
  Qed.

  (** The fiber of the classifying map is [loops K(E,3)]. *)
  Local Definition pequiv_pfiber_classifying
    : pfiber (abses_classifying_map E) <~>* loops K(E, 3)
    := loops_inv _
       o*E (pfiber2_loops (fmap (K' 3) (inclusion E))
       o*E (rt1_pfiber_delta
           o*E pequiv_pfiber (pequiv_loops_em_em B 2) pequiv_pmap_idmap
                rt1_square)).

  (** Through this identification, the fiber inclusion of the classifying map is [loops] of the projection. *)
  Local Definition rt1_pfib_square
    : pequiv_loops_em_em B 2 o* pfib (abses_classifying_map E)
      ==* fmap loops (fmap (K' 3) (projection E))
          o* pequiv_pfiber_classifying.
  Proof.
    assert (X : pfib (connecting_map (fmap (K' 3) (inclusion E))
                        (fmap (K' 3) (projection E)))
                ==* fmap loops (fmap (K' 3) (projection E))
                    o* (loops_inv _
                        o* (pfiber2_loops (fmap (K' 3) (inclusion E))
                            o* rt1_pfiber_delta))).
    { refine ((pmap_postcompose_idmap _)^* @* _).
      refine (pmap_prewhisker _
        (peisretr ((pfiber2_loops (fmap (K' 3) (projection E)))
                   o*E (pequiv_pfiber _ _
                          (square_pfib_pequiv_cxfib
                             (fmap (K' 3) (inclusion E))
                             (fmap (K' 3) (projection E))))))^* @* _).
      refine (pmap_compose_assoc _ _ _ @* _).
      refine (pmap_postwhisker _ rt1_pfiber_delta_square @* _).
      refine ((pmap_compose_assoc _ _ _)^* @* _).
      refine (pmap_prewhisker _ (pfiber2_loops_pfib2 _ _) @* _).
      refine (pmap_compose_assoc _ _ _ @* _).
      napply pmap_postwhisker.
      exact (pmap_compose_assoc _ _ _). }
    refine (square_pequiv_pfiber _ _ rt1_square @* _).
    refine (pmap_prewhisker _ X @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    napply pmap_postwhisker.
    refine (pmap_compose_assoc _ _ _ @* _).
    napply pmap_postwhisker.
    exact (pmap_compose_assoc _ _ _).
  Qed.

  (** Loop inversion is an involution. *)
  Local Definition loops_inv_inv (X : pType)
    : loops_inv X o* loops_inv X ==* pmap_idmap.
  Proof.
    snapply Build_pHomotopy.
    - intro p; exact (inv_V p).
    - reflexivity.
  Qed.

  (** Loop inversion is natural. *)
  Local Definition loops_inv_natural {X Y : pType} (f : X ->* Y)
    : fmap loops f o* loops_inv X ==* loops_inv Y o* fmap loops f.
  Proof.
    pointed_reduce_pmap f.
    snapply Build_pHomotopy.
    - intro p.
      exact (whiskerL 1 (whiskerR (ap_V f p) 1)
             @ (concat_1p _ @ concat_p1 _)
             @ (inverse2 (concat_1p _ @ concat_p1 _))^).
    - reflexivity.
  Qed.

  (** Through [pequiv_pfiber_classifying], the connecting map of the classifying map's fiber sequence is [loops] of the inclusion. *)
  Local Definition rt1_conn_square
    : pequiv_pfiber_classifying
      o* connecting_map (pfib (abses_classifying_map E))
           (abses_classifying_map E)
      ==* fmap loops (fmap (K' 3) (inclusion E)).
  Proof.
    lhs' napply pmap_compose_assoc.
    lhs' napply (pmap_postwhisker _ (pmap_compose_assoc _ _ _)).
    lhs' napply (pmap_postwhisker _
      (pmap_postwhisker _ (pmap_compose_assoc _ _ _))).
    lhs' refine (pmap_postwhisker _ (pmap_postwhisker _ (pmap_postwhisker _
      (connecting_map_natural _ _ rt1_square
       @* (pmap_postwhisker _ (fmap_id loops _)
           @* pmap_precompose_idmap _))))).
    lhs' refine (pmap_postwhisker _ (pmap_postwhisker _
      (connecting_map_natural _ _ _))).
    lhs' refine (pmap_postwhisker _ (pmap_postwhisker _
      (pmap_postwhisker _ (fmap_id loops _)
       @* pmap_precompose_idmap _))).
    lhs' napply (pmap_postwhisker _ (connecting_map_pfib2 _)).
    lhs' refine (pmap_postwhisker _
      (loops_inv_natural (fmap (K' 3) (inclusion E)))).
    lhs_V' napply pmap_compose_assoc.
    lhs' napply (pmap_prewhisker _ (loops_inv_inv _)).
    napply pmap_postcompose_idmap.
  Qed.

  (** The middle isomorphism of the round trip. *)
  Local Definition rt1_middle
    : GroupIsomorphism (abgroup_pi_pfiber 0 (abses_classifying_map E)) E.
  Proof.
    nrefine (grp_iso_compose (grp_iso_inverse (equiv_g_pi_n_em E 2)) _).
    nrefine (grp_iso_compose
      (grp_iso_inverse (groupiso_pi_loops 1 K(E, 3))) _).
    exact (groupiso_pi_functor 1 pequiv_pfiber_classifying).
  Defined.

  (** The inclusion square of the round trip. *)
  Local Definition rt1_incl_square (a : A)
    : rt1_middle (abses_pfiber_incl 0 (abses_classifying_map E) a)
      = inclusion E a.
  Proof.
    apply (equiv_inj (equiv_g_pi_n_em E 2)).
    refine (eisretr (equiv_g_pi_n_em E 2) _ @ _).
    apply (equiv_inj (groupiso_pi_loops 1 K(E, 3))).
    refine (eisretr (groupiso_pi_loops 1 K(E, 3)) _ @ _).
    assert (CORE : fmap (Pi 2) (pequiv_pfiber_classifying)
                     (fmap (Pi 2)
                        (connecting_map (pfib (abses_classifying_map E))
                           (abses_classifying_map E))
                        (groupiso_pi_loops 1 K(A, 3)
                           (equiv_g_pi_n_em A 2 a)))
                   = groupiso_pi_loops 1 K(E, 3)
                       (equiv_g_pi_n_em E 2 (inclusion E a))).
    { refine ((fmap_comp (Pi 2)
                (connecting_map (pfib (abses_classifying_map E))
                   (abses_classifying_map E))
                (pequiv_pfiber_classifying)
                (groupiso_pi_loops 1 K(A, 3)
                   (equiv_g_pi_n_em A 2 a)))^ @ _).
      refine (fmap2 (Pi 2) rt1_conn_square _ @ _).
      refine ((fmap_pi_loops 2 (fmap (K' 3) (inclusion E))
                (equiv_g_pi_n_em A 2 a))^ @ _).
      exact (ap (pi_loops 2 K(E, 3)) (pi_em_fmap (inclusion E) 2 a)). }
    exact CORE.
  Qed.

  (** The projection square of the round trip. *)
  Local Definition rt1_proj_square (x : Pi 2 (pfiber (abses_classifying_map E)))
    : abses_pfiber_proj 0 (abses_classifying_map E) x
      = projection E (rt1_middle x).
  Proof.
    apply (equiv_inj (equiv_g_pi_n_em B 1)).
    refine (eisretr (equiv_g_pi_n_em B 1) _ @ _).
    apply (equiv_inj (groupiso_pi_functor 1 (pequiv_loops_em_em B 2))).
    (* The left side, through the pointed square. *)
    refine ((fmap_comp (Pi 2) (pfib (abses_classifying_map E))
              (pequiv_loops_em_em B 2) x)^ @ _).
    refine (fmap2 (Pi 2) rt1_pfib_square x @ _).
    refine (fmap_comp (Pi 2) (pequiv_pfiber_classifying)
              (fmap loops (fmap (K' 3) (projection E))) x @ _).
    (* The right side, through naturality of [pi_loops] and [pi_em_fmap]. *)
    refine (ap (fmap (pPi 2) (fmap loops (fmap (K' 3) (projection E))))
      (eisretr (groupiso_pi_loops 1 K(E, 3))
        (fmap (Pi 2) (pequiv_pfiber_classifying) x))^ @ _).
    refine ((fmap_pi_loops 2 (fmap (K' 3) (projection E)) _)^ @ _).
    refine (ap (groupiso_pi_loops 1 K(B, 3)) _ @ _).
    { refine (ap (fmap (Pi 3) (fmap (K' 3) (projection E)))
        (eisretr (equiv_g_pi_n_em E 2) _)^ @ _).
      exact (pi_em_fmap (projection E) 2 (rt1_middle x)). }
    exact (eisretr (groupiso_pi_loops 1 K(B, 3)) _).
  Qed.

  (** The first round trip: the short exact sequence extracted from the classifying map of [E] is [E]. *)
  Definition abses_pfiber_classifying
    : abses_pfiber 0 (abses_classifying_map E) = E
    := path_abses (E := abses_pfiber 0 (abses_classifying_map E)) (F := E)
         rt1_middle rt1_incl_square rt1_proj_square.

End ClassifyingRoundTrip.

(** ** The classification theorem

[abses_classifying_map] is an equivalence, with inverse [abses_pfiber]. *)

Section Classification.
  Context `{Univalence} {B A : AbGroup@{u}}.

  (** A section of the classifying map. *)
  Local Definition abses_classifying_section (f : K(B, 2) ->* K(A, 3))
    : abses_classifying_map
        (abses_pfiber 1 ((equiv_deloop_em_pmap B A 0)^-1
           (f o* pequiv_neg_em^-1*)))
      = f.
  Proof.
    apply path_pforall.
    refine (abses_classifying_pfiber_deloop _ @* _).
    refine (pmap_prewhisker pequiv_neg_em
              (phomotopy_path (eisretr (equiv_deloop_em_pmap B A 0) _)) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (peissect pequiv_neg_em) @* _).
    apply pmap_precompose_idmap.
  Qed.

  (** The second round trip. *)
  Local Definition abses_classifying_map_pfiber (f : K(B, 2) ->* K(A, 3))
    : abses_classifying_map (abses_pfiber 0 f) = f.
  Proof.
    transitivity (abses_classifying_map
      (abses_pfiber 1 ((equiv_deloop_em_pmap B A 0)^-1
         (f o* pequiv_neg_em^-1*)))).
    - apply (ap abses_classifying_map).
      refine ((ap (abses_pfiber 0) (abses_classifying_section f))^ @ _).
      exact (abses_pfiber_classifying _).
    - exact (abses_classifying_section f).
  Qed.

  (** Short exact sequences [A -> E -> B] are classified by pointed maps [K(B,2) ->* K(A,3)]. *)
  Definition equiv_abses_classifying_map
    : AbSES B A <~> (K(B, 2) ->* K(A, 3))
    := equiv_adjointify abses_classifying_map (abses_pfiber 0)
         abses_classifying_map_pfiber abses_pfiber_classifying.

  (** Consequently [Ext B A] is the set of path components of the classifying mapping type. *)
  Definition equiv_ext_classifying
    : Ext B A <~> Tr 0 (K(B, 2) ->* K(A, 3))
    := Trunc_functor_equiv 0 equiv_abses_classifying_map.

  (** [AbSES B A] is essentially small, and so is [Ext B A] (Remark 2.2.5). *)
  Definition issmall_abses : IsSmall@{u _} (AbSES B A)
    := issmall_equiv_issmall (equiv_abses_classifying_map)^-1%equiv
         (issmall_in _).

  Definition issmall_ext : IsSmall@{u _} (Ext B A)
    := issmall_equiv_issmall (equiv_ext_classifying)^-1%equiv
         (issmall_in _).

End Classification.

(** ** Naturality of the classifying map

A morphism of short exact sequences induces a commuting square relating the two classifying maps. *)

(** Keep the [cxfib] equivalence witnesses opaque so their inverses stay inert. *)
Opaque isequiv_cxfib_em isequiv_cxfib.

Section Naturality.
  Context `{Univalence} {B A Y X : AbGroup@{u}}
    {E : AbSES B A} {F : AbSES Y X} (phi : AbSESMorphism E F).

  (** [K(-,3)] of the projection square of [phi]. *)
  Local Definition em_proj_square
    : fmap (K' 3) (projection F) o* fmap (K' 3) (component2 phi)
      ==* fmap (K' 3) (component3 phi) o* fmap (K' 3) (projection E).
  Proof.
    refine ((fmap_comp (K' 3) _ _)^* @* _ @* fmap_comp (K' 3) _ _).
    refine (phomotopy_path (ap (fun h => fmap (K' 3) h) _)).
    apply equiv_path_grouphomomorphism; intro e.
    exact (right_square phi e).
  Defined.

  (** [K(-,3)] of the inclusion square of [phi]. *)
  Local Definition em_incl_square
    : fmap (K' 3) (component2 phi) o* fmap (K' 3) (inclusion E)
      ==* fmap (K' 3) (inclusion F) o* fmap (K' 3) (component1 phi).
  Proof.
    refine ((fmap_comp (K' 3) _ _)^* @* _ @* fmap_comp (K' 3) _ _).
    refine (phomotopy_path (ap (fun h => fmap (K' 3) h) _)).
    apply equiv_path_grouphomomorphism; intro a.
    exact (left_square phi a)^.
  Defined.

  (** The fiber inclusions, as equivalences. *)
  Local Definition em_cxfib_E
    : K(A, 3) <~>* pfiber (fmap (K' 3) (projection E))
    := @pequiv_cxfib _ _ _ (fmap (K' 3) (inclusion E))
         (fmap (K' 3) (projection E)) (isexact_em_abses E 2).

  Local Definition em_cxfib_F
    : K(X, 3) <~>* pfiber (fmap (K' 3) (projection F))
    := @pequiv_cxfib _ _ _ (fmap (K' 3) (inclusion F))
         (fmap (K' 3) (projection F)) (isexact_em_abses F 2).

  (** The fiber-inclusion comparison commutes with the morphism on fibers. *)
  Local Definition em_cxfib_square
    : functor_pfiber (em_proj_square^*) o* em_cxfib_E
      = em_cxfib_F o* fmap (K' 3) (component1 phi).
  Proof.
    snapply (path_pmap_pi_connected 1).
    1,2: exact _.
    1: exact (isconnected_equiv' 2 K(X, 3) em_cxfib_F (isconnected_em 2)).
    1: exact _.
    intro x.
    refine (isinj_embedding _ (isembedding_pi_pfib_em F 2) _ _ _).
    refine (ap (fmap (Pi 3) (pfib (fmap (K' 3) (projection F))))
      (fmap_comp (Pi 3) (em_cxfib_E)
        (functor_pfiber (em_proj_square^*)) x) @ _).
    refine ((fmap_comp (Pi 3)
      (functor_pfiber (em_proj_square^*))
      (pfib (fmap (K' 3) (projection F))) _)^ @ _).
    refine ((fmap2 (Pi 3) (square_functor_pfiber (em_proj_square^*)) _)^ @ _).
    refine (fmap_comp (Pi 3) (pfib (fmap (K' 3) (projection E)))
      (fmap (K' 3) (component2 phi)) _ @ _).
    refine (ap (fmap (Pi 3) (fmap (K' 3) (component2 phi)))
      ((fmap_comp (Pi 3) (em_cxfib_E)
         (pfib (fmap (K' 3) (projection E))) x)^
       @ fmap2 (Pi 3) (pfib_cxfib _) x) @ _).
    refine ((fmap_comp (Pi 3) (fmap (K' 3) (inclusion E))
      (fmap (K' 3) (component2 phi)) x)^ @ _).
    refine (fmap2 (Pi 3) em_incl_square x @ _).
    refine (fmap_comp (Pi 3) (fmap (K' 3) (component1 phi))
      (fmap (K' 3) (inclusion F)) x @ _).
    refine ((fmap2 (Pi 3) (pfib_cxfib _)
      (fmap (Pi 3) (fmap (K' 3) (component1 phi)) x))^ @ _).
    refine (fmap_comp (Pi 3) (em_cxfib_F)
      (pfib (fmap (K' 3) (projection F))) _ @ _).
    exact (ap (fmap (Pi 3) (pfib (fmap (K' 3) (projection F))))
      (fmap_comp (Pi 3) (fmap (K' 3) (component1 phi))
        (em_cxfib_F) x))^.
  Qed.

  (** Hence the connecting maps of the two sequences are related by the morphism, through the loop identification of the bases. *)
  Local Definition cm_natural
    : fmap (K' 3) (component1 phi)
      o* connecting_map (fmap (K' 3) (inclusion E)) (fmap (K' 3) (projection E))
      ==* connecting_map (fmap (K' 3) (inclusion F)) (fmap (K' 3) (projection F))
          o* fmap loops (fmap (K' 3) (component3 phi)).
  Proof.
    refine (pmap_prewhisker _
      (moveR_pequiv_Vf em_cxfib_F (fmap (K' 3) (component1 phi))
        (functor_pfiber (em_proj_square^*) o* em_cxfib_E)
        (phomotopy_path em_cxfib_square))^* @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _) @* _).
    refine (pmap_postwhisker _ (pmap_postwhisker _
      (connecting_map_cxfib (fmap (K' 3) (inclusion E))
        (fmap (K' 3) (projection E)))) @* _).
    refine (pmap_postwhisker _
      (connecting_map_natural_functor (em_proj_square^*)) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    napply pmap_prewhisker.
    exact (moveR_pequiv_Vf em_cxfib_F
      (connecting_map (fmap (K' 3) (inclusion F)) (fmap (K' 3) (projection F)))
      (connecting_map (pfib (fmap (K' 3) (projection F)))
        (fmap (K' 3) (projection F)))
      (connecting_map_cxfib (fmap (K' 3) (inclusion F))
        (fmap (K' 3) (projection F)))^*).
  Qed.

  (** A morphism of short exact sequences induces a commuting square of classifying maps. *)
  Definition abses_classifying_map_natural
    : fmap (K' 3) (component1 phi) o* abses_classifying_map E
      ==* abses_classifying_map F o* fmap (K' 2) (component3 phi).
  Proof.
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ cm_natural @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (em_fmap_loops_natural (component3 phi) 2)
            @* _).
    exact (pmap_compose_assoc _ _ _)^*.
  Qed.

End Naturality.

Transparent isequiv_cxfib_em isequiv_cxfib.

