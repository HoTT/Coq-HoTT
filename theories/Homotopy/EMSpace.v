Require Import Basics Types.
Require Import Pointed.
Require Import Cubical.DPath.
Require Import Algebra.AbGroups.
Require Import Homotopy.Suspension.
Require Import Homotopy.ClassifyingSpace.
Require Import Homotopy.HSpace.Core.
Require Import Homotopy.HSpace.Coherent.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.Hopf.
Require Import TruncType.
Require Import Truncations.Core Truncations.Connectedness.
Require Import WildCat.

(* Formalisation of Eilenberg-MacLane spaces *)

Local Open Scope pointed_scope.
Local Open Scope nat_scope.
Local Open Scope bg_scope.
Local Open Scope mc_mult_scope.

(** The definition of the Eilenberg-Mac Lane spaces.  Note that while we allow [G] to be non-abelian for [n > 1], later results will need to assume that [G] is abelian. *)
Fixpoint EilenbergMacLane (G : Group) (n : nat) : pType
  := match n with
      | 0    => G
      | 1    => pClassifyingSpace G
      | m.+1 => pTr m.+1 (psusp (EilenbergMacLane G m))
     end.

Notation "'K(' G , n )" := (EilenbergMacLane G n).

Section EilenbergMacLane.
  Context `{Univalence}.

  Global Instance istrunc_em {G : Group} {n : nat} : IsTrunc n K(G, n).
  Proof.
    destruct n as [|[]]; exact _.
  Defined.

  Global Instance isconnected_em {G : Group} (n : nat)
    : IsConnected n K(G, n.+1).
  Proof.
    induction n; exact _.
  Defined.

  Global Instance is0connected_em {G : Group} (n : nat)
    : IsConnected 0 K(G, n.+1).
  Proof.
    rapply (is0connected_isconnected n.-2).
  Defined.

  Local Open Scope trunc_scope.

  (* This is a variant of [pequiv_ptr_loop_psusp] from pSusp.v. All we are really using is that [n.+2 <= n +2+ n], but because of the use of [isconnmap_pred_add], the proof is a bit more specific to this case. *)
  Local Lemma pequiv_ptr_loop_psusp' (X : pType) (n : nat) `{IsConnected n.+1 X}
    : pTr n.+2 X <~>* pTr n.+2 (loops (psusp X)).
  Proof.
    snrapply Build_pEquiv.
    1: rapply (fmap (pTr _) (loop_susp_unit _)).
    nrapply O_inverts_conn_map.
    nrapply (isconnmap_pred_add n.-2).
    rewrite 2 trunc_index_add_succ.
    apply (conn_map_loop_susp_unit n X).
  Defined.

  Lemma pequiv_loops_em_em (G : AbGroup) (n : nat)
    : K(G, n) <~>* loops K(G, n.+1).
  Proof.
    destruct n.
    1: apply pequiv_g_loops_bg.
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
    - reflexivity.
    - refine ((unfold_iterated_loops' _ _)^-1* o*E _ o*E IHn).
      exact (emap (iterated_loops n) (pequiv_loops_em_em _ _)).
  Defined.

  (* For positive indices, we in fact get a group isomorphism. *)
  Definition equiv_g_pi_n_em (G : AbGroup) (n : nat)
    : GroupIsomorphism G (Pi n.+1 K(G, n.+1)).
  Proof.
    induction n.
    - apply grp_iso_g_pi1_bg.
    - nrefine (grp_iso_compose _ IHn).
      nrefine (grp_iso_compose _ (groupiso_pi_functor _ (pequiv_loops_em_em _ _))).
      symmetry; apply (groupiso_pi_loops _ _).
  Defined.

  Definition iscohhspace_em {G : AbGroup} (n : nat)
    : IsCohHSpace K(G, n).
  Proof.
    nrapply iscohhspace_equiv_cohhspace.
    2: apply pequiv_loops_em_em.
    apply iscohhspace_loops.
  Defined.
  
  Definition iscohhabgroup_em {G : AbGroup} (n : nat)
    : IsCohHAbGroup K(G, n).
  Proof.
    nrapply iscohhabgroup_equiv_cohhabgroup.
    2: apply pequiv_loops_em_em.
    nrapply iscohhabgroup_equiv_cohhabgroup.
    2: exact (emap loops (pequiv_loops_em_em _ _)).
    apply iscohhabgroup_loops_loops.
  Defined.

End EilenbergMacLane.
