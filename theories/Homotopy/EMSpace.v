Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Cubical.
Require Import abstract_algebra.
Require Import TruncType.
Require Import HIT.Truncations.
Require Import HIT.Connectedness.
Require Import HIT.Suspension.
Require Import Homotopy.Freudenthal.
Require Import Homotopy.ClassifyingSpace.
Import TrM.

(* Formalisation of Eilenberg-MacLane spaces *)

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.

Section EM.
  Context `{Univalence}.

  Fixpoint EM (G : Type) `{Group G} (n : nat) : pType :=
    match n with
      | 0%nat => Build_pType G Aunit
      | 1%nat => B G
      | m.+1%nat => pTr m.+1 (psusp (EM G m))
    end.

  Global Instance istrunc_em `{Group G}  {n : nat} : IsTrunc n (EM G n).
  Proof.
    destruct n as [|[]]; exact _.
  Defined.

  Global Instance isconnected_em `{Group G} (n : nat)
    : IsConnected n (EM G n.+1).
  Proof.
    induction n; exact _.
  Defined.

  (* TODO: Move? *)
  (* TODO: better name *)
  Definition trunc_lemma (n : nat) X
    : pTr n.+2 X <~>* pTr n.+2 (pTr (n +2+ n) X).
  Proof.
    serapply Build_pEquiv'.
    2: shelve.
    serapply (BuildEquiv _ _ (Trunc_functor _ tr)).
    serapply (isequiv_conn_map_ino n.+2 _).
    apply conn_map_O_functor.
    intro x.
    serapply isconnected_pred_trunc_index_add.
    1: exact (n.-2).
    rewrite 2 trunc_index_add_succ.
    assert (p : (n .-2 +2+ n).+2 = (n +2+ n)).
    { induction n; try reflexivity; cbn.
      rewrite 2 trunc_index_add_succ.
      apply ap, ap.
      destruct n; reflexivity. }
    rewrite p.
    apply conn_map_to_O.
    Unshelve.
    1,2: reflexivity.
  Defined.

  Require Import HSpace.

  Section LicataFinsterLemma.

    Context (X : pType) `{IsConnected 0 X} `{IsTrunc 1 X} `{HSpace X}.

    (* TODO: Write about why this case cannot be justified with Freudenthal *)

    Local Definition P : Susp X -> Type
      := fun x => Tr 1 (North = x).

    Local Definition codes : Susp X -> 1 -Type.
    Proof.
      serapply Susp_rec.
      1: refine (BuildTruncType _ X).
      1: refine (BuildTruncType _ X).
      intro x.
      apply path_trunctype.
      apply (mu_l_equiv' x).
    Defined.

    Local Definition transport_codes_merid x y
      : transport codes (merid x) y = mu x y.
    Proof.
      unfold codes.
      rewrite transport_idmap_ap.
      rewrite ap_compose.
      rewrite Susp_rec_beta_merid.
      rewrite ap_trunctype.
      by rewrite transport_path_universe_uncurried.
    Defined.

    Local Definition transport_codes_merid_V x
      : transport codes (merid id)^ x = x.
    Proof.
      unfold codes.
      rewrite transport_idmap_ap.
      rewrite ap_V.
      rewrite ap_compose.
      rewrite Susp_rec_beta_merid.
      rewrite ap_trunctype.
      rewrite transport_path_universe_V_uncurried.
      apply moveR_equiv_V.
      symmetry.
      apply left_id.
    Defined.

    Local Definition encode : forall x, P x -> codes x.
    Proof.
      intro x.
      serapply Trunc_rec.
      intro p.
      exact (transport codes p id).
    Defined.

    Local Definition decode' : X -> Tr 1 (@North X = North).
    Proof.
      intro x.
      exact (tr (merid x @ (merid id)^)).
    Defined.

    Local Definition transport_decode' x y
      : transport P (merid x) (decode' y)
      = tr (merid y @ (merid id)^ @ merid x).
    Proof.
      unfold P.
      rewrite transport_compose.
      
    
      unfold decode'.
      unfold P.
      
    Admitted.

    Local Definition encode_North_decode' x : encode North (decode' x) = x.
    Proof.
      cbn.
      rewrite transport_idmap_ap.
      rewrite ap_compose.
      rewrite ap_pp.
      rewrite ap_V.
      rewrite 2 Susp_rec_beta_merid.
      rewrite <- path_trunctype_V.
      rewrite <- path_trunctype_pp.
      rewrite ap_trunctype.
      rewrite transport_path_universe_uncurried.
      apply moveR_equiv_V.
      refine (right_id _ @ (left_id _)^).
    Defined.

    Local Definition merid_mu (x y : X)
      : tr (n:=1) (merid (mu x y)) = tr (merid y @ (merid id)^ @ merid x).
    Proof.
    Admitted.

    Local Definition decode : forall x, codes x -> P x.
    Proof.
      serapply Susp_ind; cbn.
      1: apply decode'.
      { intro x.
        apply tr, merid, x. }
      intro x.
      serapply dp_path_transport^-1.
      apply dp_arrow.
      simpl; intro y.
      apply dp_path_transport.
      rewrite transport_codes_merid.
      rewrite transport_decode'.
      symmetry.
      apply merid_mu.
    Defined.

    Local Definition decode_encode : forall x (p : P x),
      decode x (encode x p) = p.
    Proof.
      intro x.
      serapply Trunc_ind.
      intro p.
      destruct p; cbv.
      apply ap, concat_pV.
    Defined.

    Lemma licata_finster : pTr 1 (loops (psusp X)) <~>* X.
    Proof.
      serapply Build_pEquiv'.
      { serapply equiv_adjointify.
        1: exact (encode North).
        1: exact decode'.
        1: intro; apply encode_North_decode'.
        intro; apply decode_encode. }
      reflexivity.
    Defined.

  End LicataFinsterLemma.

  Lemma pequiv_loops_em_em `{AbGroup G} {n : nat}
    : loops (EM G n.+1) <~>* EM G n.
  Proof.
    destruct n.
    1: apply pequiv_loops_BG_G.
    change (loops (pTr n.+2 (psusp (EM G n.+1))) <~>* EM G n.+1).
    refine (_ o*E (ptr_loops _ _)^-1*).
    destruct n.
    1: erapply licata_finster.
    transitivity (pTr n.+2 (EM G n.+2)).
    { symmetry.
      transitivity (pTr n.+2 (pTr (n +2+ n) (EM G n.+2))).
      1: generalize (EM G n.+2); intro X'; apply trunc_lemma.
      transitivity (pTr n.+2 (pTr (n +2+ n) (loops (psusp (EM G n.+2))))).
      { apply pequiv_ptr_functor.
        serapply (pequiv_ptr_loop_psusp (EM G n.+2) n). }
      symmetry.
      generalize (EM G n.+2); intro X'.
      apply trunc_lemma. }
    symmetry.
    serapply Build_pEquiv'.
    1: erapply equiv_tr.
    reflexivity.
  Defined.

End EM.
