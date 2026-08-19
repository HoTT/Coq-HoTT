From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core Equiv NatTrans Yoneda.
Require Import Pointed.
Require Import Truncations.Core Truncations.Connectedness.
Require Import HFiber.
Require Import Spaces.Int Spaces.Circle Spaces.Spheres.
From HoTT.Algebra.AbGroups Require Import AbelianGroup Z.
Require Import Algebra.Groups.ShortExactSequence.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.ExactSequence.
Require Import Homotopy.HSpace.Core.
Require Import Homotopy.HSpaceS1.
Require Import Homotopy.Hopf.
Require Import Homotopy.Join.JoinSusp.

(** * We show that the nth homotopy group of the n-sphere is the integers, for n >= 1, and that the third homotopy group of the 2-sphere is also the integers. *)

Local Open Scope wc_iso_scope.
Local Open Scope pointed_scope.

(** ** The fundamental group of the 1-sphere / circle. *)

Section Pi1S1.
  Context `{Univalence}.

  Theorem pi1_circle : Pi 1 [Circle, base] ≅ abgroup_Z.
  Proof.
    (** We give the isomorphism backwards, so we check the operation is preserved coming from the integer side. *)
    symmetry.
    srapply Build_GroupIsomorphism'.
    { equiv_via (base = base).
      2: exact (equiv_tr 0 (loops [Circle, base])).
      symmetry.
      exact equiv_loopCircle_int. }
    intros a b.
    cbn; apply ap.
    apply loopexp_add.
  Defined.

  Theorem pi1_s1 : Pi 1 (psphere 1) ≅ abgroup_Z.
  Proof.
    etransitivity.
    2: exact pi1_circle.
    apply groupiso_pi_functor.
    apply pequiv_S1_Circle.
  Defined.

End Pi1S1.

(** ** The second homotopy group of the 2-sphere is the integers. *)

Section Pi2S2.

  Definition ptr_loops_s2_s1 `{Univalence}
    : pTr 1 (loops (psphere 2)) <~>* psphere 1
    := (licata_finster (psphere 1))^-1*.

  Definition pi2_s2 `{Univalence}
    : Pi 2 (psphere 2) $<~> abgroup_Z.
  Proof.
    refine (pi1_s1 $oE _).
    change (Pi 2 ?X) with (Pi 1 (loops X)).
    symmetry; exact (grp_iso_Pi_connected_hspace (psphere 1)).
    (* The last line can also be replaced with
         exact (compose_cate (A:=Group) (emap (Pi 1) ptr_loops_s2_s1)
                                        (grp_iso_pi_Tr _ _)). *)
  Defined.

End Pi2S2.

(** ** For n >= 1, the nth homotopy group of the n-sphere is the integers. *)

Section PinSn.
  Definition pin_sn `{Univalence} (n : nat)
    : Pi n.+1 (psphere n.+1) $<~> abgroup_Z.
  Proof.
    destruct n.
    1: exact pi1_s1.
    induction n as [|n IHn].
    1: exact pi2_s2.
    refine (_ $oE groupiso_pi_loops n.+1 (psphere n.+3)).
    refine (IHn $oE _).
    symmetry.
    snapply (grp_iso_pi_connmap _ (loop_susp_unit (psphere n.+2))).
    (* The (n+2)-sphere is (n+1)-connected, so [loop_susp_unit] is [n +2+ n]-connected.  Since [n.+2 <= n +2+ n], we're done, after some [trunc_index] juggling. *)
    apply (isconnmap_pred_add n.-2).
    rewrite 2 trunc_index_add_succ.
    change (IsConnMap (Tr (n +2+ n)) (loop_susp_unit (psphere n.+2))).
    rapply conn_map_loop_susp_unit.
  Defined.
End PinSn.

(** ** The third homotopy group of the 2-sphere *)

(** We use the Hopf fibration [S1 -> S3 -> S2] to prove that the homotopy groups of [psphere 2] agree with those of [psphere 3] starting in degree 3.  In particular, [Pi 3 (psphere 2)] is isomorphic to the integers. *)

Section Pi3S2.
  Context `{Univalence}.

  (** The 1-sphere is 1-truncated by [istrunc_s1], hence [n.+1]-truncated for any [n]. *)
  Local Instance istrunc_psphere_1 (n : nat) : IsTrunc n.+1 (psphere 1)
    := @istrunc_leq 1 n.+1 tt _ _.

  (** Therefore its homotopy groups vanish in degrees 2 and above. *)
  Local Instance contr_pi_succ_succ_psphere_1 (n : nat)
    : Contr (Pi n.+2 (psphere 1))
    := contr_pi_succ_istrunc n.+1 (psphere 1).

  (** The Hopf construction on the circle gives a pointed family over [psusp (psphere 1)], which is definitionally [psphere 2].  The projection of its total space is the Hopf fibration. *)
  Definition hopf_pr1
    : psigma (hopf_construction (psphere 1)) ->* psphere 2
    := Build_pMap pr1 1.

  (** The circle, included as the fiber over the basepoint, gives a fiber sequence. *)
  Definition fiberseq_hopf
    : FiberSeq (psphere 1) (psigma (hopf_construction (psphere 1))) (psphere 2).
  Proof.
    exists hopf_pr1.
    snapply Build_pEquiv'.
    - exact (hfiber_fibration (point (psphere 2)) _).
    - reflexivity.
  Defined.

  (** The total space of the Hopf fibration is the 3-sphere. *)
  Definition pequiv_hopf_total_s3
    : psigma (hopf_construction (psphere 1)) <~>* psphere 3
    := pequiv_pjoin_sphere 1 1 o*E pequiv_hopf_total_join (psphere 1).

  (** Since the homotopy groups of the fiber [psphere 1] vanish in degrees 2 and above, the homotopy groups of [psphere 2] and [psphere 3] agree in degrees 3 and above.  The two groups flanking the relevant map in the long exact sequence are homotopy groups of [psphere 1], so [grp_iso_isexact] applies. *)
  Definition grp_iso_pi_s2_s3 (n : nat)
    : Pi n.+3 (psphere 2) $<~> Pi n.+3 (psphere 3).
  Proof.
    refine (groupiso_pi_functor n.+2 pequiv_hopf_total_s3 $oE _^-1$).
    exact (grp_iso_isexact
             (isexact_pi_total (i_fiberseq fiberseq_hopf) hopf_pr1 n.+3)
             (isexact_pi_base (i_fiberseq fiberseq_hopf) hopf_pr1 n.+2)).
  Defined.

  (** The third homotopy group of the 2-sphere is the integers. *)
  Definition pi3_s2 : Pi 3 (psphere 2) $<~> abgroup_Z
    := pin_sn 2 $oE grp_iso_pi_s2_s3 0.

End Pi3S2.
