From HoTT Require Import Basics Types Truncations.Core
  Truncations.Connectedness Truncations.SeparatedTrunc.
From HoTT.WildCat Require Import Core Equiv.
Require Import Pointed.
Require Import AbelianGroup.
Require Import Algebra.AbSES.Core Algebra.AbSES.Ext.
Require Import Universes.Smallness.
Require Import Homotopy.HomotopyGroup Homotopy.EMSpace Homotopy.ExactSequence.
Require Import Groups.Group.
Require Import HSet.
Require Import Modalities.Identity Modalities.Descent.

(** * Classification of short exact sequences

    Short exact sequences [A -> E -> B] of abelian groups are classified by
    pointed maps [K(B,2) ->* K(A,3)] (Christensen and Flaten, "Ext groups in
    homotopy type theory", Theorem 2.2.2). *)

Local Open Scope pointed_scope.

(** ** Vanishing of homotopy groups *)

(** Homotopy groups below the connectivity vanish. *)
Definition contr_pi_isconnected `{Univalence} (n : nat) (X : pType)
  `{IsConnected n X}
  : Contr (Pi n X).
Proof.
  revert X H0; induction n; intros X H0.
  - exact H0.
  - nrefine (contr_equiv' (Pi n (loops X)) _).
    1: exact (pi_loops n X)^-1*.
    napply IHn.
    rapply isconnected_loops.
Defined.

(** A successor-connectivity criterion: an [n.+1]-connected type with
    trivial [Pi n.+2] is [n.+2]-connected. *)
Definition isconnected_succ_contr_pi `{Univalence} (n : nat) (X : pType)
  `{IsConnected n.+1 X} (c : Contr (Pi n.+2 X))
  : IsConnected n.+2 X.
Proof.
  pose proof (isconnected_trunc n.+1 n.+2 (X := X)).
  nrefine (contr_equiv' K(Build_AbGroup (Pi n.+2 (pTr n.+2 X)) _, n.+2) _).
  1: exact (pequiv_em_connected_truncated (pTr n.+2 X) n.+1).
  napply contr_em_contr.
  nrefine (contr_equiv' (Pi n.+2 X) _).
  1: exact (grp_iso_pi_Tr n.+1 X).
  exact c.
  Unshelve.
  all: exact _.
Defined.

(** ** Injectivity of homotopy groups of fiber inclusions

    If the [n.+1]-st homotopy group of the double fiber of [g] vanishes,
    then [Pi n.+1] of the fiber inclusion of [g] is an embedding. *)
Instance isembedding_pi_pfib `{Univalence} {X Y : pType} (g : X ->* Y)
  (n : nat) `{Contr (Pi n.+1 (pfiber (pfib g)))}
  : IsEmbedding (fmap (Pi n.+1) (pfib g)).
Proof.
  snapply isembedding_istrivial_kernel.
  intros z w.
  pose proof (c := @center _
    (conn_map_isexact
      (i := fmap (pTr 0) (fmap (iterated_loops n.+1) (pfib (pfib g))))
      (f := fmap (pTr 0) (fmap (iterated_loops n.+1) (pfib g)))
      (z; w))).
  strip_truncations.
  destruct c as [u q].
  refine ((ap pr1 q)^ @ _).
  refine (ap _ (path_contr u (point _)) @ _).
  exact (point_eq (fmap (pTr 0) (fmap (iterated_loops n.+1)
           (pfib (pfib g))))).
Defined.

Section EMFiberSequence.
  Context `{Univalence} {B A : AbGroup@{u}} (E : AbSES B A) (n : nat).

  (** Applying [K(-,n.+1)] to a short exact sequence yields a complex. *)
  Definition iscomplex_em_abses
    : IsComplex (em_fmap (inclusion E) n.+1) (em_fmap (projection E) n.+1).
  Proof.
    refine ((em_fmap_compose (inclusion E) (projection E) n.+1)^* @* _).
    refine (phomotopy_path
      (ap (fun h => em_fmap h n.+1) (_ : _ = grp_homo_const))
      @* em_fmap_const n.+1).
    apply equiv_path_grouphomomorphism; intro a.
    exact (iscomplex_abses E a).
  Defined.

  (** The [n.+1]-st homotopy group of the double fiber of
      [em_fmap (projection E) n.+1] vanishes. *)
  Local Instance contr_pi_pfiber_pfib
    : Contr (Pi n.+1 (pfiber (pfib (em_fmap (projection E) n.+1)))).
  Proof.
    nrefine (contr_equiv' (Pi n.+2 K(B, n.+1)) _).
    1: exact (grp_iso_compose
      (groupiso_pi_functor n
        (pequiv_inverse (pfiber2_loops (em_fmap (projection E) n.+1))))
      (groupiso_pi_loops n K(B, n.+1))).
    exact (contr_pi_succ_istrunc n K(B, n.+1)).
  Defined.

  (** [Pi n.+1] of the comparison map [cxfib] is surjective. *)
  Local Definition issurj_pi_cxfib
    : IsSurjection (fmap (Pi n.+1) (cxfib iscomplex_em_abses)).
  Proof.
    intro y.
    rapply contr_inhabited_hprop.
    (* The image of [y] in [Pi n.+1 K(E, n.+1)] is killed by the projection. *)
    pose (x := fmap (Pi n.+1) (pfib (em_fmap (projection E) n.+1)) y).
    pose proof (w := cx_isexact
      (i := fmap (pTr 0) (fmap (iterated_loops n.+1)
              (pfib (em_fmap (projection E) n.+1))))
      (f := fmap (pTr 0) (fmap (iterated_loops n.+1)
              (em_fmap (projection E) n.+1)))
      y).
    (* Hence its preimage in [E] is killed by [projection E]. *)
    pose (ee := (equiv_g_pi_n_em E n)^-1 x).
    assert (pe : projection E ee = mon_unit).
    { apply (equiv_inj (equiv_g_pi_n_em B n)).
      refine ((pi_em_fmap (projection E) n ee)^ @ _).
      refine (ap (fmap (Pi n.+1) (em_fmap (projection E) n.+1))
                (eisretr (equiv_g_pi_n_em E n) x) @ _).
      refine (w @ _).
      exact (grp_homo_unit (equiv_g_pi_n_em B n))^. }
    (* By exactness, [ee] merely comes from [A]. *)
    pose proof (m := @center _ (conn_map_isexact
      (i := inclusion E) (f := projection E) (ee; pe))).
    strip_truncations.
    destruct m as [a q].
    apply tr.
    exists (equiv_g_pi_n_em A n a).
    (* The two candidates agree after the embedding [pi (pfib _)]. *)
    napply (isinj_embedding _
      (isembedding_pi_pfib (em_fmap (projection E) n.+1) n)).
    1: exact _.
    refine ((fmap_comp (Pi n.+1) (cxfib iscomplex_em_abses)
              (pfib (em_fmap (projection E) n.+1)) _)^ @ _).
    refine (fmap2 (Pi n.+1) (pfib_cxfib _) _ @ _).
    refine (pi_em_fmap (inclusion E) n a @ _).
    exact (ap (equiv_g_pi_n_em E n) (ap pr1 q) @ eisretr _ x).
  Defined.

  (** Therefore the comparison map is an equivalence: it is an isomorphism
      on [Pi n.+1], and both sides are [n]-connected and [n.+1]-truncated. *)
  Local Instance isequiv_pi_cxfib
    : IsEquiv (fmap (Pi n.+1) (cxfib iscomplex_em_abses)).
  Proof.
    apply isequiv_surj_emb.
    1: exact issurj_pi_cxfib.
    snapply isembedding_istrivial_kernel.
    intros z w.
    (* [z] is killed by [Pi n.+1] of [em_fmap (inclusion E) n.+1]. *)
    assert (wi : fmap (Pi n.+1) (em_fmap (inclusion E) n.+1) z = mon_unit).
    { refine ((fmap2 (Pi n.+1) (pfib_cxfib _) z)^ @ _).
      refine (fmap_comp (Pi n.+1) (cxfib iscomplex_em_abses)
               (pfib (em_fmap (projection E) n.+1)) z @ _).
      refine (ap (fmap (Pi n.+1) (pfib (em_fmap (projection E) n.+1))) w @ _).
      apply grp_homo_unit. }
    (* Hence [z] vanishes, since the inclusion is an embedding. *)
    pose (a := (equiv_g_pi_n_em A n)^-1 z).
    refine ((eisretr (equiv_g_pi_n_em A n) z)^ @ _).
    refine (ap (equiv_g_pi_n_em A n) (_ : a = mon_unit) @ _).
    2: apply grp_homo_unit.
    rapply (isinj_embedding (inclusion E)).
    refine (_ @ (grp_homo_unit (inclusion E))^).
    apply (equiv_inj (equiv_g_pi_n_em E n)).
    refine ((pi_em_fmap (inclusion E) n a)^ @ _).
    refine (ap (fmap (Pi n.+1) (em_fmap (inclusion E) n.+1))
              (eisretr (equiv_g_pi_n_em A n) z) @ _).
    refine (wi @ _).
    exact (grp_homo_unit (equiv_g_pi_n_em E n))^.
  Defined.

  (** Both sides of the comparison map are [n]-connected and
      [n.+1]-truncated, so it is an equivalence. *)
  Local Instance isequiv_cxfib_em : IsEquiv (cxfib iscomplex_em_abses).
  Proof.
    pose proof (isconnmap_em_fmap (projection E) n (point _)).
    (* The identification of [A] with the fiber's homotopy group. *)
    pose (psi := grp_iso_compose
      (Build_GroupIsomorphism _ _ _ isequiv_pi_cxfib)
      (equiv_g_pi_n_em A n)).
    (* The induced equivalence onto the fiber. *)
    pose (omega := pequiv_em_connected_truncated
        (pfiber (em_fmap (projection E) n.+1)) n
      o*E pequiv_em_group_iso n.+1 psi).
    (* The conjugated comparison map is [em_fmap] of an isomorphism. *)
    pose (chi := grp_iso_compose (grp_iso_inverse (equiv_g_pi_n_em A n))
      (grp_iso_compose (groupiso_pi_functor n (pequiv_inverse omega))
        (grp_iso_compose (Build_GroupIsomorphism _ _ _ isequiv_pi_cxfib)
          (equiv_g_pi_n_em A n)))).
    assert (q : em_fmap chi n.+1
                = pequiv_inverse omega o* cxfib iscomplex_em_abses).
    { apply path_em_pmap_pi; intro u.
      refine (ap (fmap (Pi n.+1) (em_fmap chi n.+1))
                (eisretr (equiv_g_pi_n_em A n) u)^ @ _).
      refine (pi_em_fmap chi n ((equiv_g_pi_n_em A n)^-1 u) @ _).
      refine (eisretr (equiv_g_pi_n_em A n) _ @ _).
      refine (ap (fun v => fmap (Pi n.+1) (pequiv_inverse omega)
                  (fmap (Pi n.+1) (cxfib iscomplex_em_abses) v))
                (eisretr (equiv_g_pi_n_em A n) u) @ _).
      exact (fmap_comp (Pi n.+1) (cxfib iscomplex_em_abses)
              (pequiv_inverse omega) u)^.
    }
    snapply (isequiv_homotopic
      (omega o (pequiv_inverse omega o* cxfib iscomplex_em_abses))).
    - napply isequiv_compose.
      2: exact _.
      exact (transport (fun (g : _ ->* _) => IsEquiv g) q
              (pointed_isequiv _ _ (pequiv_em_fmap chi n.+1))).
    - intro x; exact (eisretr omega _).
  Defined.

  (** [K(-, n.+1)] sends short exact sequences of abelian groups to fiber
      sequences of Eilenberg-Mac Lane spaces. *)
  #[export] Instance isexact_em_abses
    : IsExact purely (em_fmap (inclusion E) n.+1)
        (em_fmap (projection E) n.+1).
  Proof.
    exists iscomplex_em_abses.
    rapply conn_map_isequiv.
  Defined.

End EMFiberSequence.

(** ** The classifying map of a short exact sequence

    The connecting map of the fiber sequence [K(A,3) -> K(E,3) -> K(B,3)],
    expressed as a pointed map [K(B,2) ->* K(A,3)]. *)
Definition abses_classifying_map `{Univalence} {B A : AbGroup@{u}}
  (E : AbSES B A)
  : K(B, 2) ->* K(A, 3)
  := connecting_map (em_fmap (inclusion E) 3) (em_fmap (projection E) 3)
     o* pequiv_loops_em_em B 2.

(** ** The short exact sequence of a pointed map

    Conversely, a pointed map [f : K(B,2) ->* K(A,3)] yields a short exact
    sequence [A -> Pi 2 (pfiber f) -> B], by rotating the fiber sequence of
    [f] and taking homotopy groups. *)

(** The retraction law for [grp_iso_inverse], in the group-homomorphism
    spelling. *)
Local Definition grp_iso_retr {G H : Group} (e : GroupIsomorphism G H)
  (x : H)
  : e (grp_iso_inverse e x) = x.
Proof.
  destruct e; exact (eisretr _ x).
Defined.

(** The companion section law. *)
Local Definition grp_iso_sect {G H : Group} (e : GroupIsomorphism G H)
  (x : G)
  : grp_iso_inverse e (e x) = x.
Proof.
  destruct e; exact (eissect _ x).
Defined.

Section AbSESPfiber.
  Context `{Univalence} {B A : AbGroup@{u}} (n : nat)
    (f : K(B, n.+2) ->* K(A, n.+3)).

  (** The middle group: [Pi n.+2] of the fiber, abelian by
      Eckmann-Hilton. *)
  Definition abgroup_pi_pfiber : AbGroup
    := Build_AbGroup (Pi n.+2 (pfiber f)) _.

  (** The inclusion, through the rotated fiber sequence
      [loops K(A,n+3) -> pfiber f -> K(B,n+2)]. *)
  Definition abses_pfiber_incl : A $-> abgroup_pi_pfiber.
  Proof.
    nrefine (grp_homo_compose _
      (grp_homo_compose (groupiso_pi_loops n.+1 K(A, n.+3))
        (equiv_g_pi_n_em A n.+2))).
    exact (fmap (Pi n.+2) (connecting_map (pfib f) f)).
  Defined.

  (** The projection, induced by the fiber inclusion of [f]. *)
  Definition abses_pfiber_proj : abgroup_pi_pfiber $-> B.
  Proof.
    nrefine (grp_homo_compose
      (grp_iso_inverse (equiv_g_pi_n_em B n.+1)) _).
    exact (fmap (Pi n.+2) (pfib f)).
  Defined.

  (** The [n.+2]-nd homotopy group of the double fiber of [pfib f]
      vanishes. *)
  Local Instance contr_pi_pfiber2
    : Contr (Pi n.+2 (pfiber (pfib (pfib f)))).
  Proof.
    nrefine (contr_equiv' (Pi n.+3 K(B, n.+2)) _).
    1: exact (grp_iso_compose
      (groupiso_pi_functor n.+1 (pequiv_inverse (pfiber2_loops (pfib f))))
      (groupiso_pi_loops n.+1 K(B, n.+2))).
    exact (contr_pi_succ_istrunc n.+1 K(B, n.+2)).
  Defined.

  (** The [n.+2]-nd homotopy group of [K(A,n+3)] vanishes. *)
  Local Instance contr_pi_em : Contr (Pi n.+2 K(A, n.+3)).
  Proof.
    exact (contr_pi_isconnected n.+2 K(A, n.+3)).
  Defined.

  Local Instance isembedding_abses_pfiber_incl
    : IsEmbedding abses_pfiber_incl.
  Proof.
    snapply isembedding_istrivial_kernel.
    intros a w.
    (* The image of [a] in [Pi n.+2 (loops K(A,n+3))]. *)
    pose (z := groupiso_pi_loops n.+1 K(A, n.+3) (equiv_g_pi_n_em A n.+2 a)).
    assert (wz : fmap (Pi n.+2) ((connect_fiberseq (pfib f) f).2) z
                 = mon_unit).
    { napply (isinj_embedding _ (isembedding_pi_pfib (pfib f) n.+1)).
      1: exact _.
      refine ((fmap_comp (Pi n.+2)
                ((connect_fiberseq (pfib f) f).2 : _ ->* _)
                (pfib (pfib f)) z)^ @ _).
      refine (w @ _).
      exact (grp_homo_unit (fmap (Pi n.+2) (pfib (pfib f))))^. }
    apply (equiv_inj (equiv_g_pi_n_em A n.+2)).
    apply (equiv_inj (groupiso_pi_loops n.+1 K(A, n.+3))).
    apply (equiv_inj (groupiso_pi_functor n.+1
            ((connect_fiberseq (pfib f) f).2))).
    refine (wz @ _).
    symmetry.
    refine (ap _ (ap _ (grp_homo_unit (equiv_g_pi_n_em A n.+2))) @ _).
    refine (ap _ (grp_homo_unit (groupiso_pi_loops n.+1 K(A, n.+3))) @ _).
    exact (grp_homo_unit (groupiso_pi_functor n.+1
            ((connect_fiberseq (pfib f) f).2))).
  Defined.

  Local Definition issurjection_abses_pfiber_proj
    : IsSurjection abses_pfiber_proj.
  Proof.
    intro b.
    rapply contr_inhabited_hprop.
    pose proof (c := @center _ (conn_map_isexact
      (i := fmap (pTr 0) (fmap (iterated_loops n.+2) (pfib f)))
      (f := fmap (pTr 0) (fmap (iterated_loops n.+2) f))
      (equiv_g_pi_n_em B n.+1 b; path_contr _ _))).
    strip_truncations.
    destruct c as [u q].
    apply tr.
    exists u.
    apply (equiv_inj (equiv_g_pi_n_em B n.+1)).
    refine (grp_iso_retr (equiv_g_pi_n_em B n.+1) _ @ _).
    exact (ap pr1 q).
  Defined.

  Local Instance isexact_abses_pfiber
    : IsExact (Tr (-1)) abses_pfiber_incl abses_pfiber_proj.
  Proof.
    snapply Build_IsExact.
    - (* The composite is constant. *)
      srapply phomotopy_homotopy_hset.
      intro a.
      refine (ap (grp_iso_inverse (equiv_g_pi_n_em B n.+1)) _
              @ grp_homo_unit (grp_iso_inverse (equiv_g_pi_n_em B n.+1))).
      refine (ap (fmap (Pi n.+2) (pfib f))
        (fmap_comp (Pi n.+2) ((connect_fiberseq (pfib f) f).2 : _ ->* _)
          (pfib (pfib f)) _) @ _).
      exact (cx_isexact
        (i := fmap (pTr 0) (fmap (iterated_loops n.+2) (pfib (pfib f))))
        (f := fmap (pTr 0) (fmap (iterated_loops n.+2) (pfib f)))
        (fmap (Pi n.+2) ((connect_fiberseq (pfib f) f).2)
          (grp_homo_compose (groupiso_pi_loops n.+1 K(A, n.+3))
            (equiv_g_pi_n_em A n.+2) a))).
    - (* Every element of the kernel merely comes from [A]. *)
      intros [x w].
      rapply contr_inhabited_hprop.
      assert (w' : fmap (Pi n.+2) (pfib f) x = mon_unit).
      { refine ((grp_iso_retr (equiv_g_pi_n_em B n.+1) _)^ @ _
                @ grp_homo_unit (equiv_g_pi_n_em B n.+1)).
        exact (ap (equiv_g_pi_n_em B n.+1) w). }
      pose proof (c := @center _ (conn_map_isexact
        (i := fmap (pTr 0) (fmap (iterated_loops n.+2) (pfib (pfib f))))
        (f := fmap (pTr 0) (fmap (iterated_loops n.+2) (pfib f)))
        (x; w'))).
      strip_truncations.
      destruct c as [u q].
      apply tr.
      pose (v := fmap (Pi n.+2)
        (pequiv_inverse (connect_fiberseq (pfib f) f).2) u
        : Pi n.+2 (loops K(A, n.+3))).
      exists ((equiv_g_pi_n_em A n.+2)^-1
              ((groupiso_pi_loops n.+1 K(A, n.+3))^-1 v)).
      apply path_sigma_hprop.
      refine (ap (fmap (Pi n.+2) (connecting_map (pfib f) f))
        (ap (groupiso_pi_loops n.+1 K(A, n.+3))
          (eisretr (equiv_g_pi_n_em A n.+2) _)
         @ eisretr (groupiso_pi_loops n.+1 K(A, n.+3)) _) @ _).
      refine (fmap_comp (Pi n.+2)
        ((connect_fiberseq (pfib f) f).2 : _ ->* _)
        (pfib (pfib f)) _ @ _).
      refine (ap (fmap (Pi n.+2) (pfib (pfib f))) _ @ ap pr1 q).
      refine ((fmap_comp (Pi n.+2)
        (pequiv_inverse (connect_fiberseq (pfib f) f).2 : _ ->* _)
        ((connect_fiberseq (pfib f) f).2 : _ ->* _) u)^ @ _).
      refine (fmap2 (Pi n.+2)
        (peisretr ((connect_fiberseq (pfib f) f).2)) u @ _).
      exact (fmap_id (Pi n.+2) _ u).
  Defined.

  (** The short exact sequence associated to [f]. *)
  Definition abses_pfiber : AbSES B A
    := Build_AbSES abgroup_pi_pfiber abses_pfiber_incl abses_pfiber_proj
         _ issurjection_abses_pfiber_proj _.

End AbSESPfiber.

Section PfiberDeloop.
  Context `{Univalence} {B A : AbGroup@{u}} (psi : K(B, 3) ->* K(A, 4)).

  (** The fiber of a map [K(B,3) ->* K(A,4)] is 3-truncated. *)
  Local Instance istrunc_pfiber_em : IsTrunc 3 (pfiber psi)
    := _.

  (** Its second homotopy group is trivial: it embeds in the trivial
      [Pi 2 K(B,3)], since the second homotopy group of the double fiber
      is [Pi 3 K(A,4)], which is also trivial. *)
  Local Instance contr_pi2_pfiber_em : Contr (Pi 2 (pfiber psi)).
  Proof.
    assert (contr_pi2_pfib2 : Contr (Pi 2 (pfiber (pfib psi)))).
    { nrefine (contr_equiv' (Pi 3 K(A, 4)) _).
      1: exact (grp_iso_compose
           (groupiso_pi_functor 1 (pequiv_inverse (pfiber2_loops psi)))
           (groupiso_pi_loops 1 K(A, 4))).
      exact (contr_pi_isconnected 3 K(A, 4)). }
    apply (Build_Contr _ mon_unit).
    intro y.
    napply (isinj_embedding _ (isembedding_pi_pfib psi 1)).
    1: exact _.
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

  (** The fiber is the Eilenberg-Mac Lane space of its third homotopy
      group. *)
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
        o* pequiv_em_fmap (grp_iso_inverse eta_pfiber_psi) 3).
    exact (isequiv_compose
      (pequiv_em_fmap (grp_iso_inverse eta_pfiber_psi) 3)
      pequiv_em_pfiber_psi).
  Defined.

  (** On [Pi 3], the bridge inverts [equiv_g_pi_n_em], by construction. *)
  Local Definition pi_bridge_psi (x : Pi 3 K(abgroup_pi_pfiber 1 psi, 3))
    : fmap (Pi 3) (pequiv_em_pfiber_psi' : _ ->* _) x
      = grp_iso_inverse (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) x.
  Proof.
    refine (fmap_comp (Pi 3)
      (em_fmap (grp_iso_inverse eta_pfiber_psi) 3)
      (pequiv_em_pfiber_psi : _ ->* _) x @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi : _ ->* _))
      (ap (fmap (Pi 3) (em_fmap (grp_iso_inverse eta_pfiber_psi) 3))
        (grp_iso_retr
          (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) x)^) @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi : _ ->* _))
      (pi_em_fmap (grp_iso_inverse eta_pfiber_psi) 2 _) @ _).
    exact (grp_iso_retr eta_pfiber_psi _).
  Defined.

  (** Through the bridge, [em_fmap] of the projection is the fiber
      inclusion of [psi]. *)
  Local Definition path_em_proj_pfib_psi
    : em_fmap (abses_pfiber_proj 1 psi) 3
      = pfib psi o* pequiv_em_pfiber_psi'.
  Proof.
    snapply (path_em_pmap_pi_connected 1).
    1: exact (isconnected_em (G:=B) 2).
    1: exact _.
    intro x.
    refine (ap (fmap (Pi 3) (em_fmap (abses_pfiber_proj 1 psi) 3))
      (grp_iso_retr (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) x)^
      @ _).
    refine (pi_em_fmap (abses_pfiber_proj 1 psi) 2 _ @ _).
    refine (grp_iso_retr (equiv_g_pi_n_em B 2) _ @ _).
    refine (_ @ (fmap_comp (Pi 3)
      (pequiv_em_pfiber_psi' : _ ->* _) (pfib psi) x)^).
    exact (ap (fmap (Pi 3) (pfib psi)) (pi_bridge_psi x)^).
  Defined.

  (** Through the bridge, [em_fmap] of the inclusion is the connecting
      map of [psi], modulo the loop identification of [K(A,3)]. *)
  Local Definition path_em_incl_delta_psi
    : pequiv_em_pfiber_psi' o* em_fmap (abses_pfiber_incl 1 psi) 3
      = connecting_map (pfib psi) psi o* pequiv_loops_em_em A 3.
  Proof.
    snapply (path_em_pmap_pi_connected 1).
    1: exact _.
    1: exact _.
    intro x.
    refine (fmap_comp (Pi 3)
      (em_fmap (abses_pfiber_incl 1 psi) 3)
      (pequiv_em_pfiber_psi' : _ ->* _) x @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi' : _ ->* _))
      (ap (fmap (Pi 3) (em_fmap (abses_pfiber_incl 1 psi) 3))
        (grp_iso_retr (equiv_g_pi_n_em A 2) x)^) @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi' : _ ->* _))
      (pi_em_fmap (abses_pfiber_incl 1 psi) 2 _) @ _).
    refine (pi_bridge_psi _ @ _).
    refine (grp_iso_sect
      (equiv_g_pi_n_em (abgroup_pi_pfiber 1 psi) 2) _ @ _).
    refine (_ @ (fmap_comp (Pi 3)
      (pequiv_loops_em_em A 3 : _ ->* _)
      (connecting_map (pfib psi) psi) x)^).
    refine (ap (fmap (Pi 3) (connecting_map (pfib psi) psi)) _).
    refine (grp_iso_retr (groupiso_pi_loops 2 K(A, 4)) _ @ _).
    exact (ap (fmap (Pi 3) (pequiv_loops_em_em A 3 : _ ->* _))
      (grp_iso_retr (equiv_g_pi_n_em A 2) x)).
  Defined.

  (** The projection square as a square of pointed maps. *)
  Local Definition square_em_proj_pfib_psi
    : pequiv_pmap_idmap o* em_fmap (projection (abses_pfiber 1 psi)) 3
      ==* pfib psi o* pequiv_em_pfiber_psi'
    := pmap_postcompose_idmap _ @* phomotopy_path path_em_proj_pfib_psi.

  (** The third homotopy group of the double fiber of [pfib psi]
      vanishes, so [Pi 3] of its fiber inclusion is an embedding. *)
  Local Instance contr_pi3_pfiber2_psi
    : Contr (Pi 3 (pfiber (pfib (pfib psi))))
    := contr_pi_pfiber2 1 psi.

  (** Through the bridge, [cxfib] of the extracted sequence is the
      connecting identification of [psi], modulo the loop identification
      of [K(A,3)]. *)
  Local Definition path_cxfib_connect_psi
    : pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
        square_em_proj_pfib_psi
      o* pequiv_cxfib (i := em_fmap (inclusion (abses_pfiber 1 psi)) 3)
           (f := em_fmap (projection (abses_pfiber 1 psi)) 3)
      = (connect_fiberseq (pfib psi) psi).2 o* pequiv_loops_em_em A 3.
  Proof.
    snapply (path_em_pmap_pi_connected 1).
    1: exact (isconnected_equiv' 2 (loops K(A, 4))
         ((connect_fiberseq (pfib psi) psi).2)
         (@isconnected_loops _ 2 K(A, 4) (isconnected_em 3))).
    1: exact _.
    intro x.
    napply (isinj_embedding _ (isembedding_pi_pfib (pfib psi) 2)).
    1: exact _.
    refine (ap (fmap (Pi 3) (pfib (pfib psi)))
      (fmap_comp (Pi 3)
        (pequiv_cxfib (i := em_fmap (inclusion (abses_pfiber 1 psi)) 3)
           (f := em_fmap (projection (abses_pfiber 1 psi)) 3) : _ ->* _)
        (pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
           square_em_proj_pfib_psi : _ ->* _) x) @ _).
    refine ((fmap_comp (Pi 3)
      (pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
         square_em_proj_pfib_psi : _ ->* _)
      (pfib (pfib psi)) _)^ @ _).
    refine ((fmap2 (Pi 3)
      (square_pequiv_pfiber pequiv_em_pfiber_psi' pequiv_pmap_idmap
         square_em_proj_pfib_psi) _)^ @ _).
    refine (fmap_comp (Pi 3)
      (pfib (em_fmap (projection (abses_pfiber 1 psi)) 3))
      (pequiv_em_pfiber_psi' : _ ->* _) _ @ _).
    refine (ap (fmap (Pi 3) (pequiv_em_pfiber_psi' : _ ->* _))
      ((fmap_comp (Pi 3)
         (pequiv_cxfib (i := em_fmap (inclusion (abses_pfiber 1 psi)) 3)
            (f := em_fmap (projection (abses_pfiber 1 psi)) 3) : _ ->* _)
         (pfib (em_fmap (projection (abses_pfiber 1 psi)) 3)) x)^
       @ fmap2 (Pi 3) (pfib_cxfib _) x) @ _).
    refine ((fmap_comp (Pi 3)
      (em_fmap (abses_pfiber_incl 1 psi) 3)
      (pequiv_em_pfiber_psi' : _ ->* _) x)^ @ _).
    refine (ap (fun (m : _ ->* _) => fmap (Pi 3) m x)
      path_em_incl_delta_psi @ _).
    refine (fmap_comp (Pi 3)
      (pequiv_loops_em_em A 3 : _ ->* _)
      (connecting_map (pfib psi) psi) x @ _).
    refine (fmap_comp (Pi 3)
      ((connect_fiberseq (pfib psi) psi).2 : _ ->* _)
      (pfib (pfib psi)) _ @ _).
    exact (ap (fmap (Pi 3) (pfib (pfib psi)))
      (fmap_comp (Pi 3)
        (pequiv_loops_em_em A 3 : _ ->* _)
        ((connect_fiberseq (pfib psi) psi).2 : _ ->* _) x))^.
  Defined.

  (** The connecting identification of [psi] inverts [pfiber2_loops],
      since the underlying [pequiv_pfiber] square is tautological. *)
  Local Definition pfiber2_loops_connect_psi
    : pfiber2_loops psi o* ((connect_fiberseq (pfib psi) psi).2 : _ ->* _)
      ==* pmap_idmap.
  Proof.
    refine (pmap_prewhisker _ _ @* peisretr
      ((pfiber2_loops psi)
       o*E (pequiv_pfiber _ _ (square_pfib_pequiv_cxfib (pfib psi) psi)))).
    refine (_ @* (compose_cate_fun (A:=pType) _ _)^*).
    refine (_ @* (pmap_postwhisker _ (pequiv_pfiber_cxfib_taut psi)
                  @* pmap_precompose_idmap _)^*).
    reflexivity.
  Defined.

  (** Through the loop identification of [K(A,3)], the connecting map of
      the extracted fiber sequence is [loops psi], twisted by loop
      inversion. *)
  Local Definition connecting_map_em_loops_psi
    : pequiv_loops_em_em A 3
      o* connecting_map (em_fmap (inclusion (abses_pfiber 1 psi)) 3)
           (em_fmap (projection (abses_pfiber 1 psi)) 3)
      ==* fmap loops psi o* loops_inv K(B, 3).
  Proof.
    (* Insert the identity [pfiber2_loops psi o* connect] in front. *)
    refine ((pmap_postcompose_idmap _)^* @* _).
    refine (pmap_prewhisker _ pfiber2_loops_connect_psi^* @* _).
    (* Reassociate to expose the connecting composite, then the cxfib
       square. *)
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
  Defined.

  (** Negation on [K(B,2)], as loop inversion conjugated by the loop
      identification. *)
  Local Definition pequiv_neg_em : K(B, 2) <~>* K(B, 2)
    := (pequiv_loops_em_em B 2)^-1*
       o*E (loops_inv K(B, 3) o*E pequiv_loops_em_em B 2).

  (** Under the loop identification, [pequiv_neg_em] is loop inversion. *)
  Local Definition pequiv_neg_em_loops
    : pequiv_loops_em_em B 2 o* pequiv_neg_em
      ==* loops_inv K(B, 3) o* pequiv_loops_em_em B 2.
  Proof.
    refine (pmap_postwhisker _
      (compose_cate_fun (A:=pType) _ _) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ (peisretr (pequiv_loops_em_em B 2)) @* _).
    refine (pmap_postcompose_idmap _ @* _).
    exact (compose_cate_fun (A:=pType) _ _).
  Defined.

  (** The classifying map of the extracted sequence is the delooping
      equivalence applied to [psi], twisted by [pequiv_neg_em]. *)
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
  Defined.

End PfiberDeloop.

(** ** The first round trip

    The short exact sequence extracted from the classifying map of [E] is
    [E] itself. *)

Section ClassifyingRoundTrip.
  Context `{Univalence} {B A : AbGroup@{u}} (E : AbSES B A).

  (** The classifying map equals the connecting map after the loop
      identification, as a square. *)
  Local Definition rt1_square
    : pequiv_pmap_idmap o* abses_classifying_map E
      ==* connecting_map (em_fmap (inclusion E) 3)
            (em_fmap (projection E) 3)
          o* pequiv_loops_em_em B 2
    := pmap_postcompose_idmap _.

  (** The fiber of the connecting map's defining presentation. *)
  Local Definition rt1_pfiber_delta
    : pfiber (connecting_map (em_fmap (inclusion E) 3)
                (em_fmap (projection E) 3))
      <~>* pfiber (pfib (em_fmap (inclusion E) 3)).
  Proof.
    refine (pequiv_pfiber
      ((connect_fiberseq (em_fmap (inclusion E) 3)
          (em_fmap (projection E) 3)).2)
      pequiv_pmap_idmap _).
    exact (pmap_postcompose_idmap _).
  Defined.

  (** Its defining square. *)
  Local Definition rt1_pfiber_delta_square
    : (connect_fiberseq (em_fmap (inclusion E) 3)
         (em_fmap (projection E) 3)).2
      o* pfib (connecting_map (em_fmap (inclusion E) 3)
                 (em_fmap (projection E) 3))
      ==* pfib (pfib (em_fmap (inclusion E) 3)) o* rt1_pfiber_delta.
  Proof.
    refine (square_pequiv_pfiber
      ((connect_fiberseq (em_fmap (inclusion E) 3)
          (em_fmap (projection E) 3)).2)
      pequiv_pmap_idmap _).
  Defined.

  (** The fiber of the classifying map is [loops K(E,3)]. *)
  Local Definition pequiv_pfiber_classifying
    : pfiber (abses_classifying_map E) <~>* loops K(E, 3).
  Proof.
    snapply Build_pEquiv.
    1: exact (loops_inv _
       o* (pfiber2_loops (em_fmap (inclusion E) 3)
       o* (rt1_pfiber_delta
           o* pequiv_pfiber (pequiv_loops_em_em B 2) pequiv_pmap_idmap
                rt1_square))).
    exact _.
  Defined.

  (** Through this identification, the fiber inclusion of the classifying
      map is [loops] of the projection. *)
  Local Definition rt1_pfib_square
    : pequiv_loops_em_em B 2 o* pfib (abses_classifying_map E)
      ==* fmap loops (em_fmap (projection E) 3)
          o* pequiv_pfiber_classifying.
  Proof.
    assert (X : pfib (connecting_map (em_fmap (inclusion E) 3)
                        (em_fmap (projection E) 3))
                ==* fmap loops (em_fmap (projection E) 3)
                    o* (loops_inv _
                        o* (pfiber2_loops (em_fmap (inclusion E) 3)
                            o* rt1_pfiber_delta))).
    { refine ((pmap_postcompose_idmap _)^* @* _).
      refine (pmap_prewhisker _
        (peisretr ((pfiber2_loops (em_fmap (projection E) 3))
                   o*E (pequiv_pfiber _ _
                          (square_pfib_pequiv_cxfib
                             (em_fmap (inclusion E) 3)
                             (em_fmap (projection E) 3)))))^* @* _).
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
  Defined.

  (** Loop inversion is an involution. *)
  Local Definition loops_inv_inv (X : pType)
    : loops_inv X o* loops_inv X ==* pmap_idmap.
  Proof.
    snapply Build_pHomotopy.
    - intro p; exact (inv_V p).
    - reflexivity.
  Defined.

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
  Defined.

  (** Through [pequiv_pfiber_classifying], the connecting map of the
      classifying map's fiber sequence is [loops] of the inclusion. *)
  Local Definition rt1_conn_square
    : pequiv_pfiber_classifying
      o* connecting_map (pfib (abses_classifying_map E))
           (abses_classifying_map E)
      ==* fmap loops (em_fmap (inclusion E) 3).
  Proof.
    assert (N1 : pequiv_pfiber (pequiv_loops_em_em B 2) pequiv_pmap_idmap
                   rt1_square
                 o* connecting_map (pfib (abses_classifying_map E))
                      (abses_classifying_map E)
                 ==* connecting_map
                       (pfib (connecting_map (em_fmap (inclusion E) 3)
                                (em_fmap (projection E) 3)))
                       (connecting_map (em_fmap (inclusion E) 3)
                          (em_fmap (projection E) 3))).
    { refine (connecting_map_natural _ _ rt1_square @* _).
      refine (pmap_postwhisker _ (fmap_id loops _) @* _).
      apply pmap_precompose_idmap. }
    assert (N2 : rt1_pfiber_delta
                 o* connecting_map
                      (pfib (connecting_map (em_fmap (inclusion E) 3)
                               (em_fmap (projection E) 3)))
                      (connecting_map (em_fmap (inclusion E) 3)
                         (em_fmap (projection E) 3))
                 ==* connecting_map
                       (pfib (pfib (em_fmap (inclusion E) 3)))
                       (pfib (em_fmap (inclusion E) 3))).
    { refine (connecting_map_natural _ _ _ @* _).
      refine (pmap_postwhisker _ (fmap_id loops _) @* _).
      apply pmap_precompose_idmap. }
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _) @* _).
    refine (pmap_postwhisker _
      (pmap_postwhisker _ (pmap_compose_assoc _ _ _)) @* _).
    refine (pmap_postwhisker _ (pmap_postwhisker _
      (pmap_postwhisker _ N1)) @* _).
    refine (pmap_postwhisker _ (pmap_postwhisker _ N2) @* _).
    refine (pmap_postwhisker _ (connecting_map_pfib2 _) @* _).
    refine (pmap_postwhisker _
      (loops_inv_natural (em_fmap (inclusion E) 3)) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ (loops_inv_inv _) @* _).
    apply pmap_postcompose_idmap.
  Defined.

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
    refine (grp_iso_retr (equiv_g_pi_n_em E 2) _ @ _).
    apply (equiv_inj (groupiso_pi_loops 1 K(E, 3))).
    refine (grp_iso_retr (groupiso_pi_loops 1 K(E, 3)) _ @ _).
    assert (CORE : fmap (Pi 2) (pequiv_pfiber_classifying : _ ->* _)
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
                (pequiv_pfiber_classifying : _ ->* _)
                (groupiso_pi_loops 1 K(A, 3)
                   (equiv_g_pi_n_em A 2 a)))^ @ _).
      refine (fmap2 (Pi 2) rt1_conn_square _ @ _).
      refine ((fmap_pi_loops 2 (em_fmap (inclusion E) 3)
                (equiv_g_pi_n_em A 2 a))^ @ _).
      exact (ap (pi_loops 2 K(E, 3)) (pi_em_fmap (inclusion E) 2 a)). }
    exact CORE.
  Defined.

  (** The projection square of the round trip. *)
  Local Definition rt1_proj_square (x : Pi 2 (pfiber (abses_classifying_map E)))
    : abses_pfiber_proj 0 (abses_classifying_map E) x
      = projection E (rt1_middle x).
  Proof.
    apply (equiv_inj (equiv_g_pi_n_em B 1)).
    refine (grp_iso_retr (equiv_g_pi_n_em B 1) _ @ _).
    apply (equiv_inj (groupiso_pi_functor 1 (pequiv_loops_em_em B 2))).
    (* The left side, through the pointed square. *)
    refine ((fmap_comp (Pi 2) (pfib (abses_classifying_map E))
              (pequiv_loops_em_em B 2 : _ ->* _) x)^ @ _).
    refine (fmap2 (Pi 2) rt1_pfib_square x @ _).
    refine (fmap_comp (Pi 2) (pequiv_pfiber_classifying : _ ->* _)
              (fmap loops (em_fmap (projection E) 3)) x @ _).
    (* The right side, through naturality of [pi_loops] and [pi_em_fmap]. *)
    refine (ap (fmap (pPi 2) (fmap loops (em_fmap (projection E) 3)))
      (grp_iso_retr (groupiso_pi_loops 1 K(E, 3))
        (fmap (Pi 2) (pequiv_pfiber_classifying : _ ->* _) x))^ @ _).
    refine ((fmap_pi_loops 2 (em_fmap (projection E) 3) _)^ @ _).
    refine (ap (groupiso_pi_loops 1 K(B, 3)) _ @ _).
    { refine (ap (fmap (Pi 3) (em_fmap (projection E) 3))
        (grp_iso_retr (equiv_g_pi_n_em E 2) _)^ @ _).
      exact (pi_em_fmap (projection E) 2 (rt1_middle x)). }
    exact (grp_iso_retr (groupiso_pi_loops 1 K(B, 3)) _).
  Defined.

  (** The first round trip: the short exact sequence extracted from the
      classifying map of [E] is [E]. *)
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
  Defined.

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
  Defined.

  (** Short exact sequences [A -> E -> B] are classified by pointed maps
      [K(B,2) ->* K(A,3)]. *)
  Definition equiv_abses_classifying_map
    : AbSES B A <~> (K(B, 2) ->* K(A, 3))
    := equiv_adjointify abses_classifying_map (abses_pfiber 0)
         abses_classifying_map_pfiber abses_pfiber_classifying.

  (** Consequently [Ext B A] is the set of path components of the
      classifying mapping type. *)
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

    A morphism of short exact sequences induces a commuting square relating
    the two classifying maps. *)

(** Keep the [cxfib] equivalence witnesses opaque so their inverses stay
    inert. *)
Opaque isequiv_cxfib_em isequiv_cxfib.

Section Naturality.
  Context `{Univalence} {B A Y X : AbGroup@{u}}
    {E : AbSES B A} {F : AbSES Y X} (phi : AbSESMorphism E F).

  (** [K(-,3)] of the projection square of [phi]. *)
  Local Definition em_proj_square
    : em_fmap (projection F) 3 o* em_fmap (component2 phi) 3
      ==* em_fmap (component3 phi) 3 o* em_fmap (projection E) 3.
  Proof.
    refine ((em_fmap_compose _ _ 3)^* @* _ @* em_fmap_compose _ _ 3).
    refine (phomotopy_path (ap (fun h => em_fmap h 3) _)).
    apply equiv_path_grouphomomorphism; intro e.
    exact (right_square phi e).
  Defined.

  (** [K(-,3)] of the inclusion square of [phi]. *)
  Local Definition em_incl_square
    : em_fmap (component2 phi) 3 o* em_fmap (inclusion E) 3
      ==* em_fmap (inclusion F) 3 o* em_fmap (component1 phi) 3.
  Proof.
    refine ((em_fmap_compose _ _ 3)^* @* _ @* em_fmap_compose _ _ 3).
    refine (phomotopy_path (ap (fun h => em_fmap h 3) _)).
    apply equiv_path_grouphomomorphism; intro a.
    exact (left_square phi a)^.
  Defined.

  (** The fiber inclusions, as equivalences. *)
  Local Definition em_cxfib_E
    : K(A, 3) <~>* pfiber (em_fmap (projection E) 3)
    := @pequiv_cxfib _ _ _ (em_fmap (inclusion E) 3)
         (em_fmap (projection E) 3) (isexact_em_abses E 2).

  Local Definition em_cxfib_F
    : K(X, 3) <~>* pfiber (em_fmap (projection F) 3)
    := @pequiv_cxfib _ _ _ (em_fmap (inclusion F) 3)
         (em_fmap (projection F) 3) (isexact_em_abses F 2).

  (** The fiber-inclusion comparison commutes with the morphism on
      fibers. *)
  Local Definition em_cxfib_square
    : functor_pfiber (em_proj_square^*) o* em_cxfib_E
      = em_cxfib_F o* em_fmap (component1 phi) 3.
  Proof.
    snapply (path_em_pmap_pi_connected 1).
    1: exact (isconnected_equiv' 2 K(X, 3) em_cxfib_F (isconnected_em 2)).
    1: exact _.
    intro x.
    napply (isinj_embedding _
      (@isembedding_pi_pfib _ _ _ (em_fmap (projection F) 3) 2
        (contr_pi_pfiber_pfib F 2))).
    refine (ap (fmap (Pi 3) (pfib (em_fmap (projection F) 3)))
      (fmap_comp (Pi 3) (em_cxfib_E : _ ->* _)
        (functor_pfiber (em_proj_square^*) : _ ->* _) x) @ _).
    refine ((fmap_comp (Pi 3)
      (functor_pfiber (em_proj_square^*) : _ ->* _)
      (pfib (em_fmap (projection F) 3)) _)^ @ _).
    refine ((fmap2 (Pi 3) (square_functor_pfiber (em_proj_square^*)) _)^ @ _).
    refine (fmap_comp (Pi 3) (pfib (em_fmap (projection E) 3))
      (em_fmap (component2 phi) 3) _ @ _).
    refine (ap (fmap (Pi 3) (em_fmap (component2 phi) 3))
      ((fmap_comp (Pi 3) (em_cxfib_E : _ ->* _)
         (pfib (em_fmap (projection E) 3)) x)^
       @ fmap2 (Pi 3) (pfib_cxfib _) x) @ _).
    refine ((fmap_comp (Pi 3) (em_fmap (inclusion E) 3)
      (em_fmap (component2 phi) 3) x)^ @ _).
    refine (fmap2 (Pi 3) em_incl_square x @ _).
    refine (fmap_comp (Pi 3) (em_fmap (component1 phi) 3)
      (em_fmap (inclusion F) 3) x @ _).
    refine ((fmap2 (Pi 3) (pfib_cxfib _)
      (fmap (Pi 3) (em_fmap (component1 phi) 3) x))^ @ _).
    refine (fmap_comp (Pi 3) (em_cxfib_F : _ ->* _)
      (pfib (em_fmap (projection F) 3)) _ @ _).
    exact (ap (fmap (Pi 3) (pfib (em_fmap (projection F) 3)))
      (fmap_comp (Pi 3) (em_fmap (component1 phi) 3)
        (em_cxfib_F : _ ->* _) x))^.
  Qed.

  (** Hence the connecting maps of the two sequences are related by the
      morphism, through the loop identification of the bases. *)
  Local Definition cm_natural
    : em_fmap (component1 phi) 3
      o* connecting_map (em_fmap (inclusion E) 3) (em_fmap (projection E) 3)
      ==* connecting_map (em_fmap (inclusion F) 3) (em_fmap (projection F) 3)
          o* fmap loops (em_fmap (component3 phi) 3).
  Proof.
    refine (pmap_prewhisker _
      (moveR_pequiv_Vf em_cxfib_F (em_fmap (component1 phi) 3)
        (functor_pfiber (em_proj_square^*) o* em_cxfib_E)
        (phomotopy_path em_cxfib_square))^* @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (pmap_compose_assoc _ _ _) @* _).
    refine (pmap_postwhisker _ (pmap_postwhisker _
      (connecting_map_cxfib (em_fmap (inclusion E) 3)
        (em_fmap (projection E) 3))) @* _).
    refine (pmap_postwhisker _
      (connecting_map_natural_functor (em_proj_square^*)) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    napply pmap_prewhisker.
    exact (moveR_pequiv_Vf em_cxfib_F
      (connecting_map (em_fmap (inclusion F) 3) (em_fmap (projection F) 3))
      (connecting_map (pfib (em_fmap (projection F) 3))
        (em_fmap (projection F) 3))
      (connecting_map_cxfib (em_fmap (inclusion F) 3)
        (em_fmap (projection F) 3))^*).
  Defined.

  (** A morphism of short exact sequences induces a commuting square of
      classifying maps. *)
  Definition abses_classifying_map_natural
    : em_fmap (component1 phi) 3 o* abses_classifying_map E
      ==* abses_classifying_map F o* em_fmap (component3 phi) 2.
  Proof.
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ cm_natural @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (em_fmap_loops_natural (component3 phi) 2)
            @* _).
    exact (pmap_compose_assoc _ _ _)^*.
  Defined.

End Naturality.

Transparent isequiv_cxfib_em isequiv_cxfib.

