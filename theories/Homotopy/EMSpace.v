Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import abstract_algebra.
Require Import HIT.Truncations.
Require Import HIT.Suspension.
Require Import HIT.Connectedness.
Require Import Homotopy.ClassifyingSpace.
Import TrM.

(* Formalisation of Eilenberg-MacLane spaces *)

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.

Section EilenbergMacLane.
  Context `{Univalence}.

  Fixpoint EilenbergMacLane (G : Type) `{Group G} (n : nat) : pType :=
    match n with
      | 0%nat => Build_pType G Aunit
      | 1%nat => B G
      | m.+1%nat => pTr m.+1 (psusp (EilenbergMacLane G m))
    end.

  Notation "'K(' G , n )" := (EilenbergMacLane G n).

  Global Instance istrunc_em `{Group G}  {n : nat} : IsTrunc n K(G, n).
  Proof.
    destruct n as [|[]]; exact _.
  Defined.

  Global Instance isconnected_em `{Group G} (n : nat)
    : IsConnected n K(G, n.+1).
  Proof.
    induction n; exact _.
  Defined.

  (* This is a straight forward property of truncations. Most of the proof is spent getting the indexing to work correctly. *)
  Local Definition trunc_lemma (n : nat) X
    : pTr n.+2 X <~>* pTr n.+2 (pTr (n +2+ n) X).
  Proof.
    serapply Build_pEquiv'.
    { serapply (BuildEquiv _ _ (Trunc_functor _ tr)).
      serapply (isequiv_conn_map_ino n.+2 _).
      apply conn_map_O_functor.
      intro x.
      serapply (isconnected_pred_trunc_index_add (n.-2)).
      rewrite 2 trunc_index_add_succ.
      (* This has to be done by induction since n.-2.+2 only cancels when n >= 0 i.e. a nat *)
      assert (p : (n .-2 +2+ n).+2 = (n +2+ n)).
      { induction n; try reflexivity; cbn.
        rewrite 2 trunc_index_add_succ.
        apply ap, ap.
        destruct n; reflexivity. }
      destruct p.
      apply conn_map_to_O. }
    all: reflexivity.
  Defined.

  Lemma pequiv_loops_em_em `{AbGroup G} {n : nat}
    : loops K(G, n.+1) <~>* K(G, n).
  Proof.
    destruct n.
    1: apply pequiv_loops_BG_G.
    change (loops (pTr n.+2 (psusp (EilenbergMacLane G n.+1))) <~>* EilenbergMacLane G n.+1).
    refine (_ o*E (ptr_loops _ _)^-1*).
    destruct n.
    1: serapply licata_finster.
    transitivity (pTr n.+2 (EilenbergMacLane G n.+2)).
    { symmetry.
      transitivity (pTr n.+2 (pTr (n +2+ n) (EilenbergMacLane G n.+2))).
      1: generalize (EilenbergMacLane G n.+2); intro X'; apply trunc_lemma.
      transitivity (pTr n.+2 (pTr (n +2+ n) (loops (psusp (EilenbergMacLane G n.+2))))).
      { apply pequiv_ptr_functor.
        serapply (pequiv_ptr_loop_psusp (EilenbergMacLane G n.+2) n). }
      symmetry.
      generalize (EilenbergMacLane G n.+2); intro X'.
      apply trunc_lemma. }
    symmetry.
    serapply Build_pEquiv'.
    1: serapply equiv_tr.
    reflexivity.
  Defined.

End EilenbergMacLane.
