From HoTT Require Import Basics Types Truncations.Core HFiber.
From HoTT.WildCat Require Import Core Equiv.
Require Import Pointed.
Require Import AbelianGroup AbHom.
Require Import Algebra.AbSES.Core Algebra.AbSES.Pullback Algebra.AbSES.BaerSum.
Require Import Homotopy.HomotopyGroup Homotopy.ClassifyingSpace Homotopy.EMSpace
  Homotopy.Cover.
Require Import Modalities.ReflectiveSubuniverse Modalities.Modality.
Require Import Groups.Group.

Local Open Scope pointed_scope.
Local Open Scope mc_add_scope.

(** * The fundamental group of [AbSES B A]

    [AbSES.Core] gives an equivalence of types
    [loops_abses : (B $-> A) <~> loops (AbSES B A)].  We show that it is an
    isomorphism of groups: concatenation of loops corresponds to addition of
    homomorphisms.  The Baer sum laws hold at the level of [AbSES B A], so
    translation by [E] is a self-equivalence taking the split sequence to
    [E], and the fundamental group is [ab_hom B A] at every basepoint.  It
    follows that each path component of [AbSES B A] is a classifying space
    [K(ab_hom B A, 1)]. *)

Section LoopGroup.
  Context `{Univalence} {B A : AbGroup@{u}}.

  (** The path data on the split sequence corresponding to [f : B $-> A].
      [loops_abses f] is definitionally [equiv_path_abses_iso (tdata f)], and
      the underlying automorphism of [tdata f] sends [(a, b)] to
      [(a + f b, mon_unit + b)]. *)
  Local Definition tdata (f : B $-> A)
    : abses_path_data_iso (point (AbSES B A)) (point (AbSES B A))
    := equiv_path_abses_data _ _ (abses_endomorphism_trivial^-1 f).

  (** [loops_abses] is additive: composition of path data on the split
      sequence corresponds to addition of the off-diagonal homomorphisms. *)
  Definition loops_abses_add (f g : B $-> A)
    : loops_abses (f + g) = loops_abses f @ loops_abses g.
  Proof.
    refine (_ @ (abses_path_data_compose_beta (tdata f) (tdata g))^).
    napply (ap equiv_path_abses_iso).
    rapply path_sigma_hprop.
    rapply equiv_path_groupisomorphism.
    intros [a b].
    (* LHS: [(a + (f b + g b), 0 + b)];  RHS: [((a + f b) + g (0 + b), 0 + (0 + b))]. *)
    snapply path_prod'; cbn.
    - exact (associativity a (f b) (g b)
               @ ap (fun w => (a + f b) + w) (ap g (left_identity b))^).
    - exact (ap (fun z => mon_unit + z) (left_identity b))^.
  Defined.

  (** The fundamental group of [AbSES B A] at the split sequence. *)
  Definition grp_iso_pi1_abses
    : GroupIsomorphism (ab_hom B A) (Pi 1 (AbSES B A)).
  Proof.
    snapply Build_GroupIsomorphism.
    - snapply Build_GroupHomomorphism.
      + exact (fun f => tr (loops_abses f)).
      + intros f g.
        exact (ap tr (loops_abses_add f g)).
    - exact (equiv_isequiv (equiv_tr 0 _ oE loops_abses)).
  Defined.

End LoopGroup.

(** * Translation by a short exact sequence *)

Section Translation.
  Context `{Univalence} {B A : AbGroup@{u}}.

  (** Translation by [E] under the Baer sum is a self-equivalence of
      [AbSES B A], with inverse given by translation by the Baer inverse
      [abses_pullback (- grp_homo_id) E]. *)
  Definition equiv_abses_translate (E : AbSES B A)
    : AbSES B A <~> AbSES B A.
  Proof.
    srapply equiv_adjointify.
    - exact (fun F => abses_baer_sum F E).
    - exact (fun F => abses_baer_sum F (abses_pullback (- grp_homo_id) E)).
    - intro F.
      refine (baer_sum_associative _ _ _ @ _).
      refine (ap (abses_baer_sum F) (baer_sum_inverse_r E) @ _).
      apply baer_sum_unit_r.
    - intro F.
      refine (baer_sum_associative _ _ _ @ _).
      refine (ap (abses_baer_sum F) (baer_sum_inverse_l E) @ _).
      apply baer_sum_unit_r.
  Defined.

  (** Translation takes the split sequence to [E]. *)
  Definition pequiv_abses_translate (E : AbSES B A)
    : AbSES B A <~>* [AbSES B A, E]
    := Build_pEquiv' (equiv_abses_translate E) (baer_sum_unit_l E).

  (** The fundamental group of [AbSES B A] at any basepoint is [ab_hom B A],
      even though [E] need not be merely equal to the split sequence. *)
  Definition grp_iso_pi1_abses_at (E : AbSES B A)
    : GroupIsomorphism (ab_hom B A) (Pi 1 [AbSES B A, E])
    := grp_iso_compose
         (groupiso_pi_functor 0 (pequiv_abses_translate E))
         grp_iso_pi1_abses.

End Translation.

(** * Components of [AbSES B A] are classifying spaces *)

Section Component.
  Context `{Univalence} {B A : AbGroup@{u}} (E : AbSES B A).

  (** The inclusion of the component of [E] is an embedding, since being in
      a given component is a proposition. *)
  Local Instance isembedding_pcomp_abses
    : IsEmbedding (pr1 : pcomp (AbSES B A) E -> AbSES B A).
  Proof.
    intro F.
    exact (istrunc_equiv_istrunc _ (hfiber_fibration F _)).
  Qed.

  Local Instance isconnected_pcomp_abses
    : IsConnected (Tr 0) (pcomp (AbSES B A) E)
    := _.

  Local Instance istrunc_pcomp_abses
    : IsTrunc 1 (pcomp (AbSES B A) E)
    := _.

  (** The inclusion of the component of [E] induces an isomorphism of
      fundamental groups. *)
  Definition grp_iso_pi1_pcomp_abses
    : GroupIsomorphism (Pi 1 (pcomp (AbSES B A) E)) (Pi 1 [AbSES B A, E]).
  Proof.
    snapply Build_GroupIsomorphism.
    - snapply Build_GroupHomomorphism.
      + exact (Trunc_functor 0 (ap pr1)).
      + intros p q; strip_truncations.
        exact (ap tr (ap_pp pr1 p q)).
    - exact _.
  Defined.

  (** Each component of [AbSES B A] is a classifying space of [ab_hom B A]. *)
  Definition pequiv_pcomp_abses_em
    : pcomp (AbSES B A) E <~>* K(ab_hom B A, 1).
  Proof.
    refine (_ o*E (pequiv_pclassifyingspace_pi1 (pcomp (AbSES B A) E))^-1*).
    exact (emap pClassifyingSpace
             (grp_iso_compose
                (grp_iso_inverse (grp_iso_pi1_abses_at E))
                grp_iso_pi1_pcomp_abses)).
  Defined.

End Component.
