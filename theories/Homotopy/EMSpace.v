Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Cubical.DPath.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Truncations.
Require Import Homotopy.Suspension.
Require Import Homotopy.ClassifyingSpace.
Require Import Homotopy.HSpace.
Require Import TruncType.
Require Import UnivalenceImpliesFunext.
Import TrM.

(* Formalisation of Eilenberg-MacLane spaces *)

Local Open Scope pointed_scope.
Local Open Scope nat_scope.
Local Open Scope bg_scope.
Local Open Scope mc_mult_scope.


(** When X is 0-connected we see that Freudenthal doesn't let us characterise the loop space of a suspension. For this we need some extra assumptions about our space X.

Suppose X is a 0-connected, 1-truncated coherent H-space, then

  pTr 1 (loops (psusp X)) <~>* X

By coherent H-space we mean that left and right identity laws at the unit are the same.
*)

Section LicataFinsterLemma.

  Context `{Univalence} (X : pType)
    `{IsConnected 0 X} `{IsTrunc 1 X} `{IsHSpace X}
    {coh : left_identity mon_unit = right_identity mon_unit}.

  (** This encode-decode style proof is detailed in Eilenberg-MacLane Spaces in Homotopy Type Theory by Dan Licata and Eric Finster *)

  Local Definition P : Susp X -> Type
    := fun x => Tr 1 (North = x).

  Local Definition codes : Susp X -> 1 -Type.
  Proof.
    serapply Susp_rec.
    1: refine (BuildTruncType _ X).
    1: refine (BuildTruncType _ X).
    intro x.
    apply path_trunctype.
    apply (equiv_hspace_left_op x).
  Defined.

  Local Definition transport_codes_merid x y
    : transport codes (merid x) y = x * y.
  Proof.
    unfold codes.
    rewrite transport_idmap_ap.
    rewrite ap_compose.
    rewrite Susp_rec_beta_merid.
    rewrite ap_trunctype.
    by rewrite transport_path_universe_uncurried.
  Defined.

  Local Definition transport_codes_merid_V x
    : transport codes (merid mon_unit)^ x = x.
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
    cbn; apply left_identity.
  Defined.

  Local Definition encode : forall x, P x -> codes x.
  Proof.
    intro x.
    serapply Trunc_rec.
    intro p.
    exact (transport codes p mon_unit).
  Defined.

  Local Definition decode' : X -> Tr 1 (@North X = North).
  Proof.
    intro x.
    exact (tr (merid x @ (merid mon_unit)^)).
  Defined.

  Local Definition transport_decode' x y
    : transport P (merid x) (decode' y)
    = tr (merid y @ (merid mon_unit)^ @ merid x).
  Proof.
    unfold P.
    unfold decode'.
    rewrite transport_compose.
    generalize (merid x).
    generalize (merid y @ (merid mon_unit)^).
    intros p [].
    cbn; apply ap.
    symmetry.
    apply concat_p1.
  Defined.

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
    apply moveR_equiv_V; cbn.
    exact (right_identity _ @ (left_identity _)^).
  Defined.

  Local Definition merid_mu (x y : X)
    : tr (n:=1) (merid (x * y)) = tr (merid y @ (merid mon_unit)^ @ merid x).
  Proof.
    set (Q := fun a b => tr (n:=1) (merid (a * b))
      = tr (merid b @ (merid mon_unit)^ @ merid a)).
    serapply (@wedge_incl_elim_uncurried _ (-1) (-1) _
      mon_unit _ _ mon_unit _ Q _ _ x y).
    { intros a b.
      cbn; unfold Q.
      apply istrunc_paths.
      exact _. }
    unfold Q.
    srefine (_;_;_).
    { intro b.
      apply ap.
      symmetry.
      refine (concat_pp_p _ _ _ @ _).
      refine (ap _ (concat_Vp _) @ _).
      refine (concat_p1 _ @ _).
      apply ap.
      exact (left_identity b)^. }
    { intro a.
      apply ap.
      symmetry.
      refine (ap (fun x => concat x (merid a)) (concat_pV _) @ _).
      refine (concat_1p _ @ _).
      apply ap.
      exact (right_identity a)^. }
    simpl.
    apply ap, ap.
    rewrite <- coh.
    rewrite ? concat_p_pp.
    apply whiskerR.
    generalize (merid mon_unit).
    by intros [].
  Defined.

  Local Definition decode : forall x, codes x -> P x.
  Proof.
    serapply Susp_ind; cbn.
    1: apply decode'.
    { intro x.
      apply tr, merid, x. }
    intro x.
    serapply dp_path_transport^-1.
    apply dp_arrow.
    intro y.
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

  (* We could call this pequiv_ptr_loop_psusp but since we already used that for the Freudenthal case, it seems appropriate to name licata_finster for this one case *)
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


Section EilenbergMacLane.
  Context `{Univalence}.

  Fixpoint EilenbergMacLane (G : Group) (n : nat) : pType
    := match n with
        | 0    => Build_pType G _
        | 1    => pClassifingSpace G
        | m.+1 => pTr m.+1 (psusp (EilenbergMacLane G m))
       end.

  Notation "'K(' G , n )" := (EilenbergMacLane G n).

  Global Instance istrunc_em {G : Group}  {n : nat} : IsTrunc n K(G, n).
  Proof.
    destruct n as [|[]]; exact _.
  Defined.

  Global Instance isconnected_em {G : Group} (n : nat)
    : IsConnected n K(G, n.+1).
  Proof.
    induction n; exact _.
  Defined.

  Local Open Scope trunc_scope.

  (* This is a straight forward property of truncations. Most of the proof is spent getting the indexing to work correctly. *)
  Local Definition trunc_lemma (n : nat) X
    : pTr n.+2 X <~>* pTr n.+2 (pTr (n +2+ n) X).
  Proof.
    serapply Build_pEquiv'.
    { notypeclasses refine (Build_Equiv _ _ (Trunc_functor _ tr) _).
      notypeclasses refine (isequiv_conn_map_ino n.+2 _).
      1,2: exact _.
      apply conn_map_O_functor.
      intro x.
      notypeclasses refine (isconnected_pred_add n.-2 _ _).
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

  Lemma pequiv_loops_em_em (G : AbGroup) (n : nat)
    : loops K(G, n.+1) <~>* K(G, n).
  Proof.
    destruct n.
    1: apply pequiv_loops_bg_g.
    change (loops (pTr n.+2 (psusp (K(G, n.+1)))) <~>* K(G, n.+1)).
    refine (_ o*E (ptr_loops _ _)^-1* ).
    destruct n.
    { serapply licata_finster.
      reflexivity. }
    transitivity (pTr n.+2 (K(G, n.+2))).
    { symmetry.
      transitivity (pTr n.+2 (pTr (n +2+ n) (K(G, n.+2)))).
      1: generalize (K(G, n.+2)); intro X'; apply trunc_lemma.
      transitivity (pTr n.+2 (pTr (n +2+ n) (loops (psusp (K(G, n.+2)))))).
      { apply pequiv_ptr_functor.
        serapply (pequiv_ptr_loop_psusp (K(G, n.+2)) n). }
      symmetry.
      generalize (K(G, n.+2)); intro X'.
      apply trunc_lemma. }
    symmetry.
    serapply Build_pEquiv'.
    1: serapply equiv_tr.
    reflexivity.
  Defined.

End EilenbergMacLane.


