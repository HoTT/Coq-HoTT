From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core Equiv NatTrans Yoneda.
Require Import Pointed.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Spaces.Int Spaces.Circle Spaces.Spheres.
From HoTT.Algebra.AbGroups Require Import AbelianGroup Z.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.HSpaceS1.
Require Import Homotopy.Hopf.

(** * We show that the nth homotopy group of the n-sphere is the integers, for n >= 1. *)

Local Open Scope wc_iso_scope.
Local Open Scope pointed_scope.

(** The fundamental group of the 1-sphere / circle. *)

Section Pi1S1.
  Context `{Univalence}.

  Local Open Scope pointed_scope.

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

(** The second homotopy group of the 2-sphere is the integers. *)

Section Pi2S2.

  Definition ptr_loops_s2_s1 `{Univalence}
    : pTr 1 (loops (psphere 2)) <~>* psphere 1
    := (licata_finster (psphere 1))^-1*.

  Definition pi2_s2 `{Univalence}
    : Pi 2 (psphere 2) $<~> abgroup_Z.
  Proof.
    refine (pi1_s1 $oE _).
    change (Pi 2 ?X) with (Pi 1 (loops X)).
    refine (compose_cate (b:=Pi 1 (pTr 1 (loops (psphere 2)))) _ _).
    1: exact (emap (Pi 1) ptr_loops_s2_s1).
    apply grp_iso_pi_Tr.
  Defined.

End Pi2S2.

(** For n >= 1, the nth homotopy group of the n-sphere is the integers. *)

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
    exact _. (* [conn_map_loop_susp_unit] *)
  Defined.
End PinSn.
