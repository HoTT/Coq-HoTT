From HoTT Require Import Basics Types.
Require Import Pointed.
Require Import Cubical.DPath.
Require Import Algebra.AbGroups.
Require Import Homotopy.Suspension.
Require Import Homotopy.ClassifyingSpace.
Require Import Homotopy.HSpace.Coherent.
Require Import Homotopy.HomotopyGroup.
Require Import Homotopy.Hopf.
Require Import Truncations.Core Truncations.Connectedness.
Require Import WildCat.

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

  (** If [G] and [G'] are isomorphic, then [K(G,n)] and [K(G',n)] are equivalent.  TODO:  We should show that [K(-,n)] is a functor, which implies this. *)
  Definition pequiv_em_group_iso {G G' : Group} (n : nat)
    (e : G $<~> G')
    : K(G, n) <~>* K(G', n).
  Proof.
    by destruct (equiv_path_group e).
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
   <~>* pTr n.+2 (psusp (loops X))
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
