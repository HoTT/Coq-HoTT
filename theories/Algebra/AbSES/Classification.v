From HoTT Require Import Basics Types HFiber Truncations.Core
  Truncations.SeparatedTrunc.
From HoTT.WildCat Require Import Core PointedCat.
Require Import Pointed.
Require Import AbelianGroup.
Require Import AbSES.Core AbSES.Ext.
Require Import Spaces.Nat.Core.
Require Import Universes.Smallness.
Require Import Homotopy.HomotopyGroup Homotopy.EMSpace Homotopy.ExactSequence.
Require Import Homotopy.WhiteheadsPrinciple.
Require Import Groups.Group.
Require Import Equiv.BiInv.
Require Import Modalities.Identity Modalities.Descent.
Require Import Modalities.ReflectiveSubuniverse.

(** * Classification of short exact sequences *)

(** Short exact sequences [A -> E -> B] of abelian groups are classified by pointed maps [K(B,2) ->* K(A,3)] (Christensen and Flaten, "Ext groups in homotopy type theory", Theorem 2.2.2). *)

Local Open Scope pointed_scope.

(** ** Applying [(K-, n.+1)] to a short exact sequence of an abelian groups gives a fiber sequence *)

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
    1,2: srapply phomotopy_homotopy_hset; intro x;
           apply moveR_equiv_V; apply pi_em_fmap'.
    exact _.
  Defined.

  (** [K(-, n.+1)] sends short exact sequences of abelian groups to fiber sequences of Eilenberg-Mac Lane spaces.  The hypotheses of [isexact_purely_isexact_pi] are found by typeclass search: the spaces are [n]-connected and [n.+1]-truncated, [fmap (K' n.+1)] of the projection is [n]-connected since the projection is surjective, and [fmap (K' n.+1)] of the inclusion is an embedding on [Pi n.+1] since the inclusion is an embedding. *)
  #[export] Instance isexact_em_abses
    : IsExact purely (fmap (K' n.+1) (inclusion E))
        (fmap (K' n.+1) (projection E))
    := isexact_purely_isexact_pi n
        (fmap_iscomplex (K' n.+1) (iscomplex_abses E))
        isexact_pi_em_abses.

End EMFiberSequence.

(** ** The classifying map of a short exact sequence *)

(** We associate to each short exact sequence [A -> E -> B] the connecting map of the fiber sequence [K(A,3) -> K(E,3) -> K(B,3)], expressed as a pointed map [K(B,2) ->* K(A,3)]. *)
Definition abses_classifying_map `{Univalence} {B A : AbGroup@{u}}
  (E : AbSES B A)
  : K(B, 2) ->* K(A, 3)
  := connecting_map (fmap (K' 3) (inclusion E)) (fmap (K' 3) (projection E))
     o* pequiv_loops_em_em B 2.

(** ** The short exact sequence of a pointed map *)

(** Conversely, a pointed map [f : K(B,2) ->* K(A,3)] yields a short exact sequence [A -> Pi 2 (pfiber f) -> B], by rotating the fiber sequence of [f] and taking homotopy groups.  We prove this with [2] replaced by [n.+2] for any [n : nat]. *)

Section AbSESPfiber.
  Context `{Univalence} {B A : AbGroup@{u}} {n : nat}
    (f : K(B, n.+2) ->* K(A, n.+3)).

  (** The inclusion of the short exact sequence is given by the composite of the identification of [A] with [Pi n.+2 (loops K(A, n.+3))] and [Pi n.+2] applied to the connecting map [loops K(A,n+3) -> pfiber f] of the fiber sequence. *)
  Definition abses_pfiber_incl : A $-> abgroup_pi n (pfiber f)
    := fmap (Pi n.+2) (connecting_map (pfib f) f)
        $o equiv_g_pi_n_loops_em A n.+1.

  (** The projection is similarly induced by the fiber inclusion of [f]. *)
  Definition abses_pfiber_proj : abgroup_pi n (pfiber f) $-> B
    := grp_iso_inverse (equiv_g_pi_n_em B n.+1)
        $o fmap (Pi n.+2) (pfib f).

  (** The two homotopy groups neighbouring the sequence vanish: [Pi n.+2 K(A, n.+3)] lies below the connectivity of [K(A, n.+3)], and [Pi n.+3 K(B, n.+2)] lies above the truncation level of [K(B, n.+2)]. *)
  Local Instance contr_pi_em_below : Contr (Pi n.+2 K(A, n.+3))
    := contr_pi_isconnected n.+2 K(A, n.+3).

  Local Instance contr_pi_em_above : Contr (Pi n.+3 K(B, n.+2))
    := contr_pi_istrunc n.+2 K(B, n.+2).

  (** The three conditions defining a short exact sequence therefore come from the long exact sequences of the fiber sequence of [f] and of its rotation. *)

  Local Instance isembedding_abses_pfiber_incl : IsEmbedding abses_pfiber_incl.
  Proof.
    napply (istruncmap_compose (-1) (equiv_g_pi_n_loops_em A n.+1)).
    2: rapply istruncmap_mapinO_tr.
    exact (isembedding_fmap_pi_isexact (connecting_map (pfib f) f) (pfib f)
             n.+1).
  Defined.

  Local Instance issurjection_abses_pfiber_proj
    : IsSurjection abses_pfiber_proj.
  Proof.
    napply conn_map_compose.
    2: rapply conn_map_isequiv.
    exact (issurj_fmap_pi_isexact (pfib f) f n.+2).
  Defined.

  Local Instance isexact_abses_pfiber
    : IsExact (Tr (-1)) abses_pfiber_incl abses_pfiber_proj.
  Proof.
    napply (isexact_square_if _ (equiv_g_pi_n_loops_em A n.+1)
      pequiv_pmap_idmap (equiv_g_pi_n_em B n.+1)).
    3: exact (isexact_pi_total (connecting_map (pfib f) f) (pfib f) n.+2).
    (* The first square commutes by definition.  We give the term, since [reflexivity] is very slow here. *)
    1: srapply phomotopy_homotopy_hset; intro x;
         exact (idpath (abses_pfiber_incl x)).
    srapply phomotopy_homotopy_hset; intro x.
    exact (eisretr (equiv_g_pi_n_em B n.+1) _).
  Defined.

  (** The short exact sequence associated to [f]. *)
  Definition abses_pfiber : AbSES B A
    := Build_AbSES (abgroup_pi n (pfiber f)) abses_pfiber_incl abses_pfiber_proj
         _ _ _.

End AbSESPfiber.

(** ** The classifying map of the sequence of a delooped map *)

(** Rather than proving that the other composite is the identity, we will define an a priori different section of [abses_classifying_map].  To do this, we first show that for [psi : K(B,3) ->* K(A,4)], the classifying map of [abses_pfiber psi] is [fmap loops psi], twisted by negation on [K(B,2)].  Since every map [K(B,2) ->* K(A,3)] can be delooped to such a [psi], this will give a section of [abses_classifying_map] in [abses_classifying_section] below. *)

Section PfiberDeloop.
  Context `{Univalence} {B A : AbGroup@{u}} (psi : K(B, 3) ->* K(A, 4)).

  (** The fiber of a map from a 2-connected type to a 3-connected type is 2-connected. *)
  Local Instance isconnected_pfiber_em : IsConnected 2 (pfiber psi)
    := OO_isconnected_hfiber (Tr 3%nat) (Tr 2%nat) psi pt.

  (** The fiber is the Eilenberg-Mac Lane space of its third homotopy group, by [pequiv_em_connected_truncated], and on [Pi 3] that identification inverts [equiv_g_pi_n_em]. *)
  Local Definition fmap_pi_pequiv_em_pfiber
    (x : Pi 3 K(abgroup_pi 1 (pfiber psi), 3))
    : fmap (Pi 3) (pequiv_em_connected_truncated (pfiber psi) 2) x
      = (equiv_g_pi_n_em (abgroup_pi 1 (pfiber psi)) 2)^-1 x
    := fmap_pi_pequiv_em_connected_truncated (pfiber psi) 2 x.

  (** Through that identification, [fmap (K' 3)] of the projection is the fiber inclusion of [psi]. *)
  Local Definition phomotopy_em_proj_pfib
    : fmap (K' 3) (abses_pfiber_proj psi)
      ==* pfib psi o* pequiv_em_connected_truncated (pfiber psi) 2.
  Proof.
    rapply (phomotopy_pmap_pi_connected 2).
    intro x.
    lhs tapply (pi_em_fmap' (abses_pfiber_proj psi) 2).
    lhs napply (eisretr (equiv_g_pi_n_em B 2)).
    rhs tapply (fmap_comp (Pi 3)).
    tapply (ap _ (fmap_pi_pequiv_em_pfiber x)^).
  Qed.

  (** Through that identification, [fmap (K' 3)] of the inclusion is the connecting map of [psi], modulo the loop identification of [K(A,3)].  We state this using the description of the connecting map from [connecting_map_pfib]. *)
  Local Definition phomotopy_em_incl_pfib
    : pequiv_em_connected_truncated (pfiber psi) 2
        o* fmap (K' 3) (abses_pfiber_incl psi)
      ==* pfib (pfib psi)
          o* ((pfiber2_loops psi)^-1* o* pequiv_loops_em_em A 3).
  Proof.
    rhs_V' napply pmap_compose_assoc.
    rhs_V' napply (pmap_prewhisker _ (connecting_map_pfib psi)).
    rapply (phomotopy_pmap_pi_connected 2).
    intro x.
    lhs tapply (fmap_comp (Pi 3)).
    lhs tapply (ap _ (pi_em_fmap' (abses_pfiber_incl psi) 2 x)).
    lhs napply fmap_pi_pequiv_em_pfiber.
    lhs napply (eissect (equiv_g_pi_n_em (abgroup_pi 1 (pfiber psi)) 2)).
    rhs tapply (fmap_comp (Pi 3)).
    refine (ap (fmap (Pi 3) (connecting_map (pfib psi) psi)) _).
    tapply (ap _ (eisretr (equiv_g_pi_n_em A 2) x)).
  Qed.

  (** The projection square as a square of pointed maps. *)
  Local Definition square_em_proj_pfib
    : pequiv_pmap_idmap o* fmap (K' 3) (projection (abses_pfiber psi))
      ==* pfib psi o* pequiv_em_connected_truncated (pfiber psi) 2
    := pmap_postcompose_idmap _ @* phomotopy_em_proj_pfib.

  (** The two squares above form a map from the fiber sequence of Eilenberg-Mac Lane spaces of the extracted sequence to the fiber sequence of [pfib psi]. *)
  Local Definition phomotopy_cxfib_em_pfib
    : functor_pfiber square_em_proj_pfib
      o* pequiv_cxfib (i := fmap (K' 3) (inclusion (abses_pfiber psi)))
           (f := fmap (K' 3) (projection (abses_pfiber psi)))
      ==* pequiv_cxfib (i := pfib (pfib psi)) (f := pfib psi)
          o* ((pfiber2_loops psi)^-1* o* pequiv_loops_em_em A 3).
  Proof.
    (* Writing this as a single term is slower for some reason. *)
    napply (phomotopy_functor_pfiber_cxfib 2).
    4: exact phomotopy_em_incl_pfib.
    all: exact _.
  Defined.

  (** Through the loop identification of [K(A,3)], the connecting map of the extracted fiber sequence is [loops psi], twisted by loop inversion. *)
  Local Definition connecting_map_em_loops
    : pequiv_loops_em_em A 3
      o* connecting_map (fmap (K' 3) (inclusion (abses_pfiber psi)))
           (fmap (K' 3) (projection (abses_pfiber psi)))
      ==* fmap loops psi o* loops_inv K(B, 3).
  Proof.
    (* By [connecting_map_pfib2], it suffices to compare with the connecting map of the fiber sequence of [pfib psi], which we do by naturality. *)
    rhs_V' napply (connecting_map_pfib2 psi).
    napply moveL_pequiv_Mf.
    lhs_V' napply pmap_compose_assoc.
    lhs' napply (connecting_map_natural_isexact phomotopy_cxfib_em_pfib).
    lhs' tapply (pmap_postwhisker _ (fmap_id loops _)).
    napply pmap_precompose_idmap.
  Qed.

  (** Negation on [K(B,2)], as loop inversion conjugated by the loop identification.  It should agree with [fmap (K' 2) ab_homo_negation], since both act by inversion on [Pi 2], but we do not need that here. *)
  Local Definition pequiv_neg_em : K(B, 2) <~>* K(B, 2)
    := (pequiv_loops_em_em B 2)^-1*
       o*E (loops_inv K(B, 3) o*E pequiv_loops_em_em B 2).

  (** Under the loop identification, [pequiv_neg_em] is loop inversion. *)
  Local Definition pequiv_neg_em_loops
    : pequiv_loops_em_em B 2 o* pequiv_neg_em
      ==* loops_inv K(B, 3) o* pequiv_loops_em_em B 2
    := moveR_pequiv_Mf _ _ _ (reflexivity _).

  (** The classifying map of the extracted sequence is [equiv_loops_em_pmap] applied to [psi], twisted by [pequiv_neg_em]. *)
  Local Definition abses_classifying_pfiber_loop
    : abses_classifying_map (abses_pfiber psi)
      ==* equiv_loops_em_pmap B A 0 psi o* pequiv_neg_em.
  Proof.
    rhs' napply (pmap_prewhisker pequiv_neg_em
                   (equiv_loops_em_pmap_unfold B A 0 psi)
                 @* pmap_compose_assoc _ _ _
                 @* pmap_postwhisker _ (pmap_compose_assoc _ _ _)).
    lhs' napply (pmap_prewhisker _
      (moveL_pequiv_Vf _ _ _ connecting_map_em_loops)).
    lhs' napply pmap_compose_assoc.
    lhs' napply (pmap_postwhisker _ (pmap_compose_assoc _ _ _)).
    napply pmap_postwhisker.
    napply pmap_postwhisker.
    symmetry; exact pequiv_neg_em_loops.
  Qed.

End PfiberDeloop.

(** ** The first round trip *)

(** The short exact sequence extracted from the classifying map of [E] is [E] itself. *)

Section ClassifyingRoundTrip.
  Context `{Univalence} {B A : AbGroup@{u}} (E : AbSES B A).

  (** The classifying map equals the connecting map after the loop identification, as a square. *)
  Local Definition square_classifying_map
    : pequiv_pmap_idmap o* abses_classifying_map E
      ==* connecting_map (fmap (K' 3) (inclusion E))
            (fmap (K' 3) (projection E))
          o* pequiv_loops_em_em B 2
    := pmap_postcompose_idmap _.

  (** The fiber of the classifying map is [loops K(E,3)]: it is the fiber of the connecting map, which [pfib_connecting_map] identifies with the loop space of the total space. *)
  Local Definition pequiv_pfiber_classifying_map
    : pfiber (abses_classifying_map E) <~>* loops K(E, 3)
    := (loops_inv _
        o*E (pfiber2_loops (fmap (K' 3) (inclusion E))
        o*E pequiv_pfiber_connecting_map (fmap (K' 3) (inclusion E))
              (fmap (K' 3) (projection E))))
       o*E pequiv_pfiber (pequiv_loops_em_em B 2) pequiv_pmap_idmap
             square_classifying_map.

  (** Through this identification, the fiber inclusion of the classifying map is [loops] of the projection. *)
  Local Definition square_pfib_classifying_map
    : pequiv_loops_em_em B 2 o* pfib (abses_classifying_map E)
      ==* fmap loops (fmap (K' 3) (projection E))
          o* pequiv_pfiber_classifying_map.
  Proof.
    lhs' napply (square_pequiv_pfiber _ _ square_classifying_map).
    lhs' napply (pmap_prewhisker _ (pfib_connecting_map _ _)).
    napply pmap_compose_assoc.
  Qed.

  (** Through the same identification, the connecting map of the fiber sequence of the classifying map is [loops] of the inclusion. *)
  Local Definition connecting_map_classifying_map
    : pequiv_pfiber_classifying_map
      o* connecting_map (pfib (abses_classifying_map E))
           (abses_classifying_map E)
      ==* fmap loops (fmap (K' 3) (inclusion E)).
  Proof.
    lhs' napply pmap_compose_assoc.
    lhs' napply (pmap_postwhisker _
      (connecting_map_natural_idmap square_classifying_map)).
    napply connecting_map_pfib_connecting_map.
  Qed.

  (** The middle isomorphism of the round trip. *)
  Local Definition grp_iso_pi_pfiber_classifying_map
    : GroupIsomorphism (abgroup_pi 0 (pfiber (abses_classifying_map E))) E
    := grp_iso_compose (grp_iso_inverse (equiv_g_pi_n_loops_em E 1))
         (groupiso_pi_functor 1 pequiv_pfiber_classifying_map).

  (** It commutes with the inclusions. *)
  Local Definition grp_iso_pi_pfiber_classifying_map_inclusion (a : A)
    : grp_iso_pi_pfiber_classifying_map
        (abses_pfiber_incl (abses_classifying_map E) a)
      = inclusion E a.
  Proof.
    apply moveR_equiv_V.
    lhs_V exact (fmap_comp (Pi 2)
      (connecting_map (pfib (abses_classifying_map E))
        (abses_classifying_map E))
      pequiv_pfiber_classifying_map (equiv_g_pi_n_loops_em A 1 a)).
    lhs tapply (fmap2 (Pi 2) connecting_map_classifying_map).
    napply pi_loops_em_fmap.
  Qed.

  (** It commutes with the projections. *)
  Local Definition grp_iso_pi_pfiber_classifying_map_projection
    (x : Pi 2 (pfiber (abses_classifying_map E)))
    : abses_pfiber_proj (abses_classifying_map E) x
      = projection E (grp_iso_pi_pfiber_classifying_map x).
  Proof.
    apply moveR_equiv_V.
    apply (equiv_inj (groupiso_pi_functor 1 (pequiv_loops_em_em B 2))).
    (* The left side, through the pointed square. *)
    lhs_V tapply (fmap_comp (Pi 2)).
    lhs tapply (fmap2 (Pi 2) square_pfib_classifying_map).
    lhs tapply (fmap_comp (Pi 2)).
    (* The right side, by naturality of [equiv_g_pi_n_loops_em]. *)
    rhs_V napply (pi_loops_em_fmap (projection E) 1).
    tapply (ap (fmap (Pi 2) (fmap loops (fmap (K' 3) (projection E))))).
    symmetry; napply eisretr.
  Qed.

  (** The first round trip: the short exact sequence extracted from the classifying map of [E] is [E]. *)
  Definition abses_pfiber_classifying
    : abses_pfiber (abses_classifying_map E) = E
    := path_abses (E := abses_pfiber (abses_classifying_map E)) (F := E)
         grp_iso_pi_pfiber_classifying_map
         grp_iso_pi_pfiber_classifying_map_inclusion
         grp_iso_pi_pfiber_classifying_map_projection.

End ClassifyingRoundTrip.

(** ** The classification theorem *)

(** [abses_classifying_map] is an equivalence, with inverse [abses_pfiber]. *)

Section Classification.
  Context `{Univalence} {B A : AbGroup@{u}}.

  (** A section of the classifying map. *)
  Local Definition abses_classifying_section (f : K(B, 2) ->* K(A, 3))
    : abses_classifying_map
        (abses_pfiber ((equiv_loops_em_pmap B A 0)^-1
           (f o* pequiv_neg_em^-1*)))
      = f.
  Proof.
    apply path_pforall.
    lhs' napply abses_classifying_pfiber_loop.
    lhs' napply (pmap_prewhisker _
      (phomotopy_path (eisretr (equiv_loops_em_pmap B A 0) _))).
    lhs' napply pmap_compose_assoc.
    lhs' napply (pmap_postwhisker _ (peissect pequiv_neg_em)).
    apply pmap_precompose_idmap.
  Qed.

  (** The map [abses_classifying_map] has a retraction [abses_pfiber] by [abses_pfiber_classifying] and a section by [abses_classifying_section].  Therefore it is an equivalence.  This proof uses [abses_pfiber] as the inverse. *)
  #[export] Instance isequiv_abses_classifying_map
    : IsEquiv (abses_classifying_map (A:=A) (B:=B)).
  Proof.
    snapply isequiv_isbiinv.
    exact (Build_IsBiInv _ _ _ _ _ abses_classifying_section
             abses_pfiber_classifying).
  Defined.

  (** Short exact sequences [A -> E -> B] are classified by pointed maps [K(B,2) ->* K(A,3)]. *)
  Definition equiv_abses_classifying_map
    : AbSES B A <~> (K(B, 2) ->* K(A, 3))
    := Build_Equiv _ _ abses_classifying_map _.

  (** Consequently [Ext B A] is the set of path components of the classifying mapping type. *)
  Definition equiv_ext_classifying
    : Ext B A <~> Tr 0 (K(B, 2) ->* K(A, 3))
    := Trunc_functor_equiv 0 equiv_abses_classifying_map.

  (** [AbSES B A] is essentially small, and so is [Ext B A]. *)
  #[export] Instance issmall_abses : IsSmall@{u _} (AbSES B A)
    := Build_IsSmall _ _ (equiv_abses_classifying_map)^-1%equiv.

  #[export] Instance issmall_ext : IsSmall@{u _} (Ext B A)
    := Build_IsSmall _ _ (equiv_ext_classifying)^-1%equiv.

End Classification.

(** ** Naturality of the classifying map *)

(** A morphism of short exact sequences induces a commuting square relating the two classifying maps. *)

Section Naturality.
  Context `{Univalence} {B A Y X : AbGroup@{u}}
    {E : AbSES B A} {F : AbSES Y X} (phi : AbSESMorphism E F).

  (** [K(-,3)] of the projection square of [phi]. *)
  Local Definition em_proj_square
    : fmap (K' 3) (projection F) o* fmap (K' 3) (component2 phi)
      ==* fmap (K' 3) (component3 phi) o* fmap (K' 3) (projection E)
    := (fmap_comp (K' 3) _ _)^* @* fmap2 (K' 3) (right_square phi)
       @* fmap_comp (K' 3) _ _.

  (** [K(-,3)] of the inclusion square of [phi]. *)
  Local Definition em_incl_square
    : fmap (K' 3) (component2 phi) o* fmap (K' 3) (inclusion E)
      ==* fmap (K' 3) (inclusion F) o* fmap (K' 3) (component1 phi)
    := (fmap_comp (K' 3) _ _)^* @* fmap2 (K' 3) (fun a => (left_square phi a)^)
       @* fmap_comp (K' 3) _ _.

  (** The two squares above form a map between the fiber sequences of Eilenberg-Mac Lane spaces. *)
  Local Definition phomotopy_cxfib_em
    : functor_pfiber (em_proj_square^* )
      o* pequiv_cxfib (i := fmap (K' 3) (inclusion E))
           (f := fmap (K' 3) (projection E))
      ==* pequiv_cxfib (i := fmap (K' 3) (inclusion F))
            (f := fmap (K' 3) (projection F))
          o* fmap (K' 3) (component1 phi)
    := phomotopy_functor_pfiber_cxfib 2 em_incl_square (em_proj_square^* ).

  (** A morphism of short exact sequences induces a commuting square of classifying maps, by naturality of the connecting map and of the loop identification. *)
  Definition abses_classifying_map_natural
    : fmap (K' 3) (component1 phi) o* abses_classifying_map E
      ==* abses_classifying_map F o* fmap (K' 2) (component3 phi).
  Proof.
    lhs_V' napply pmap_compose_assoc.
    lhs' napply (pmap_prewhisker _
      (connecting_map_natural_isexact phomotopy_cxfib_em)).
    lhs' napply pmap_compose_assoc.
    lhs' napply (pmap_postwhisker _ (em_fmap_loops_natural (component3 phi) 2)).
    exact (pmap_compose_assoc _ _ _)^*.
  Qed.

End Naturality.
