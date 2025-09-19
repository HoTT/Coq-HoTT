From HoTT Require Import Basics.
Require Import Types.
Require Import WildCat.
Require Import Pointed.Core.
Require Import Pointed.Loops.
Require Import Pointed.pTrunc.
Require Import Pointed.pEquiv.
Require Import Homotopy.Suspension.
Require Import Homotopy.BlakersMassey.
Require Import Truncations.

Generalizable Variables X A B f g n.

Local Open Scope path_scope.
Local Open Scope pointed_scope.

(** ** Pointedness of [Susp] and path spaces thereof *)
(** We arbitrarily choose [North] to be the point. *)
Instance ispointed_susp {X : Type} : IsPointed (Susp X) | 0
  := North.

Instance ispointed_path_susp `{IsPointed X}
  : IsPointed (North = South :> Susp X) | 0 := merid (point X).

Instance ispointed_path_susp' `{IsPointed X}
  : IsPointed (South = North :> Susp X) | 0 := (merid (point X))^.

Definition psusp (X : Type) : pType
  := [Susp X, _].

(** ** Suspension Functor *)

(** [psusp] has a functorial action. *)
(** TODO: make this a displayed functor *)
Instance is0functor_psusp : Is0Functor psusp
  := Build_Is0Functor _ _ _ _ psusp (fun X Y f
      => Build_pMap (functor_susp f) 1).

(** [psusp] is a 1-functor. *)
Instance is1functor_psusp : Is1Functor psusp.
Proof.
  snapply Build_Is1Functor.
  (** Action on 2-cells *)
  - intros X Y f g p.
    pointed_reduce.
    srapply Build_pHomotopy.
    { simpl.
      srapply Susp_ind.
      1,2: reflexivity.
      intro x; cbn.
      rewrite transport_paths_FlFr.
      rewrite concat_p1.
      rewrite 2 Susp_rec_beta_merid.
      destruct (p x).
      apply concat_Vp. }
    reflexivity.
  (** Preservation of identity. *)
  - intros X.
    srapply Build_pHomotopy.
    { srapply Susp_ind; try reflexivity.
      intro x.
      refine (transport_paths_FFlr _ _ @ _).
      by rewrite ap_idmap, Susp_rec_beta_merid,
        concat_p1, concat_Vp. }
    reflexivity.
  (** Preservation of composition. *)
  - pointed_reduce_rewrite; srefine (Build_pHomotopy _ _); cbn.
    { srapply Susp_ind; try reflexivity; cbn.
      intros x.
      refine (transport_paths_FlFr _ _ @ _).
      rewrite concat_p1; apply moveR_Vp.
      by rewrite concat_p1, ap_compose, !Susp_rec_beta_merid. }
    reflexivity.
Defined.

(** ** Loop-Suspension Adjunction *)

Module Book_Loop_Susp_Adjunction.

  (** Here is the proof of the adjunction isomorphism given in the book (6.5.4); we put it in a non-exported module for reasons discussed below. *)
  Definition loop_susp_adjoint `{Funext} (A B : pType)
  : (psusp A ->* B) <~> (A ->* loops B).
  Proof.
    refine (_ oE (issig_pmap (psusp A) B)^-1).
    refine (_ oE (equiv_functor_sigma_pb
                 (Q := fun NSm => fst NSm.1 = point B)
                 (equiv_Susp_rec A B))).
    transitivity {bp : {b:B & b = point B} & {b:B & A -> bp.1 = b} }.
    1:make_equiv.
    refine (_ oE equiv_contr_sigma _); simpl.
    refine (_ oE (equiv_sigma_contr
                   (A := {p : B & A -> point B = p})
                   (fun pm => { q : point B = pm.1 & pm.2 (point A) = q }))^-1).
    make_equiv_contr_basedpaths.
  Defined.

  (** Unfortunately, with this definition it seems to be quite hard to prove that the isomorphism is natural on pointed maps.  The following proof gets partway there, but ends with a pretty intractable goal.  It's also quite slow, so we don't want to compile it all the time. *)
  (**
<<
  Definition loop_susp_adjoint_nat_r `{Funext} (A B B' : pType)
             (f : psusp A ->* B) (g : B ->* B')
  : loop_susp_adjoint A B' (g o* f)
    ==* fmap loops g o* loop_susp_adjoint A B f.
  Proof.
    pointed_reduce. (* Very slow for some reason. *)
    exact (Build_pHomotopy _ _).
    - intros a. simpl.
      exact (_ @ (concat_1p _)^).
      exact (_ @ (concat_p1 _)^).
      rewrite !transport_sigma. simpl.
      rewrite !(transport_arrow_fromconst (B := A)).
      rewrite !transport_paths_Fr.
      rewrite !ap_V, !ap_pr1_path_basedpaths.
      Fail rewrite ap_pp, !(ap_compose f g), ap_V. (* This line fails with current versions of the library. *)
      Fail reflexivity.
      admit.
    - cbn.
      Fail reflexivity.
  Abort.
>>
   *)

End Book_Loop_Susp_Adjunction.

(** Thus, instead we will construct the adjunction in terms of a unit and counit natural transformation. *)

Definition loop_susp_unit (X : pType) : X ->* loops (psusp X)
  := Build_pMap (fun x => merid x @ (merid (point X))^) (concat_pV _).

(** By Freudenthal, we have that this map is (2n+2)-connected when [X] is (n+1)-connected. *)
Instance conn_map_loop_susp_unit `{Univalence} (n : trunc_index)
  (X : pType) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (loop_susp_unit X).
Proof.
  exact (conn_map_compose _ merid (equiv_concat_r (merid pt)^ _)).
Defined.

(** We also have this corollary: *)
Definition pequiv_ptr_loop_psusp `{Univalence} (X : pType) n `{IsConnected n.+1 X}
  : pTr (n +2+ n) X <~>* pTr (n +2+ n) (loops (psusp X)).
Proof.
  snapply Build_pEquiv.
  1:exact (fmap (pTr _) (loop_susp_unit _)).
  rapply O_inverts_conn_map.
Defined.

Definition loop_susp_unit_natural {X Y : pType} (f : X ->* Y)
  : loop_susp_unit Y o* f
  ==* fmap loops (fmap psusp f) o* loop_susp_unit X.
Proof.
  pointed_reduce.
  snapply Build_pHomotopy; cbn.
  - intros x; symmetry.
    lhs napply concat_1p; lhs napply concat_p1.
    lhs napply (ap_pV _ (merid x) (merid point0)).
    exact (Susp_rec_beta_merid _ @@ inverse2 (Susp_rec_beta_merid _)).
  - cbn. apply moveL_pV.
    rhs napply concat_1p.
    apply moveR_Vp.
    lhs napply concat_p1.
    (* Handle the [ap ... (1 @ q)] part. *)
    lhs napply (ap_compose (fun p => ap _ p @ 1) _ (concat_pV _)).
    lhs_V napply concat_1p_1.
    rhs napply concat_pp_p.
    apply whiskerL.
    (* Handle the [ap ... (q @ 1)] part. *)
    lhs napply (ap_compose _ (fun q => q @ 1) (concat_pV _)).
    lhs_V napply concat_p1_1.
    rhs napply concat_pp_p.
    apply whiskerL.
    (* Finish it off. *)
    symmetry.
    lhs napply concat_pp_p.
    exact (ap_ap_concat_pV _ _ _ (Susp_rec_beta_merid point0)).
Defined.

Definition loop_susp_counit (X : pType) : psusp (loops X) ->* X
  := Build_pMap (Susp_rec (point X) (point X) idmap) 1.

Definition loop_susp_counit_natural {X Y : pType} (f : X ->* Y)
  : f o* loop_susp_counit X
  ==* loop_susp_counit Y o* fmap psusp (fmap loops f).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); simpl.
  - simple refine (Susp_ind _ _ _ _); cbn; try reflexivity; intros p.
    rewrite transport_paths_FlFr, ap_compose, concat_p1.
    apply moveR_Vp.
    refine (ap_compose
              (Susp_rec North South (fun x0 => merid (1 @ (ap f x0 @ 1))))
              (Susp_rec (point Y) (point Y) idmap) (merid p) @ _).
    do 2 rewrite Susp_rec_beta_merid.
    refine (concat_1p _ @ _). f_ap. f_ap. symmetry.
    exact (Susp_rec_beta_merid _).
  - reflexivity.
Qed.

(** Now the triangle identities *)

Definition loop_susp_triangle1 (X : pType)
  : fmap loops (loop_susp_counit X) o* loop_susp_unit (loops X)
  ==* pmap_idmap.
Proof.
  (* This proof has a lot of overlap with [loop_susp_unit_natural]. Can a common lemma be factored out? *)
  snapply Build_pHomotopy.
  - intros p; cbn.
    lhs napply concat_1p; lhs napply concat_p1.
    lhs napply (ap_pV _ (merid p) _).
    lhs napply (Susp_rec_beta_merid _ @@ inverse2 (Susp_rec_beta_merid _)).
    apply concat_p1.
  - simpl.
    do 2 rhs napply concat_p1.
    rhs napply (ap_compose (fun p => ap _ p @ 1) _ (concat_pV _)).
    rhs_V napply (concat_1p_1 _ _).
    apply whiskerL.
    rhs napply (ap_compose _ (fun q => q @ 1) (concat_pV _)).
    rhs_V napply concat_p1_1.
    apply whiskerL.
    exact (ap_ap_concat_pV _ _ _ (Susp_rec_beta_merid pt)).
Defined. (* A bit slow, ~0.09s. *)

Definition loop_susp_triangle2 (X : pType)
  : loop_susp_counit (psusp X) o* fmap psusp (loop_susp_unit X)
  ==* pmap_idmap.
Proof.
  simple refine (Build_pHomotopy _ _);
  [ simple refine (Susp_ind _ _ _ _) | ]; try reflexivity; cbn.
  - exact (merid (point X)).
  - intros x.
    rewrite transport_paths_FlFr, ap_idmap, ap_compose.
    rewrite Susp_rec_beta_merid.
    apply moveR_pM; rewrite concat_p1.
    refine (inverse2 (Susp_rec_beta_merid _) @ _).
    rewrite inv_pp, inv_V; reflexivity.
Qed.

(** Now we can finally construct the adjunction equivalence. *)

Definition loop_susp_adjoint `{Funext} (A B : pType)
  : (psusp A ->** B) <~>* (A ->** loops B).
Proof.
  snapply Build_pEquiv'.
  - refine (equiv_adjointify
              (fun f => fmap loops f o* loop_susp_unit A)
              (fun g => loop_susp_counit B o* fmap psusp g) _ _).
    + intros g. apply path_pforall.
      lhs' exact (pmap_prewhisker _ (fmap_comp loops _ _)).
      lhs' apply pmap_compose_assoc.
      lhs' exact (pmap_postwhisker _ (loop_susp_unit_natural g)^* ).
      lhs_V' apply pmap_compose_assoc.
      lhs' exact (pmap_prewhisker g (loop_susp_triangle1 B)).
      apply pmap_postcompose_idmap.
    + intros f. apply path_pforall.
      lhs' exact (pmap_postwhisker _ (fmap_comp psusp _ _)).
      lhs_V' apply pmap_compose_assoc.
      lhs' exact (pmap_prewhisker _ (loop_susp_counit_natural f)^* ).
      lhs' apply pmap_compose_assoc.
      lhs' exact (pmap_postwhisker f (loop_susp_triangle2 A)).
      apply pmap_precompose_idmap.
  - apply path_pforall.
    unfold equiv_adjointify, equiv_fun.
    lhs' exact (pmap_prewhisker _ fmap_loops_pconst).
    tapply cat_zero_l.
Defined.

(** And its naturality is easy. *)

Definition loop_susp_adjoint_nat_r `{Funext} (A B B' : pType)
  (f : psusp A ->* B) (g : B ->* B') : loop_susp_adjoint A B' (g o* f)
  ==* fmap loops g o* loop_susp_adjoint A B f.
Proof.
  cbn.
  rhs_V' apply pmap_compose_assoc.
  apply pmap_prewhisker.
  exact (fmap_comp loops f g).
Defined.

Definition loop_susp_adjoint_nat_l `{Funext} (A A' B : pType)
  (f : A ->* loops B) (g : A' ->* A) : (loop_susp_adjoint A' B)^-1 (f o* g)
  ==* (loop_susp_adjoint A B)^-1 f o* fmap psusp g.
Proof.
  cbn.
  rhs' apply pmap_compose_assoc.
  apply pmap_postwhisker.
  exact (fmap_comp psusp g f).
Defined.

Instance is1natural_loop_susp_adjoint_r `{Funext} (A : pType)
  : Is1Natural (opyon (psusp A)) (opyon A o loops)
      (loop_susp_adjoint A).
Proof.
  snapply Build_Is1Natural.
  intros B B' g f.
  rhs_V rapply cat_assoc_strong.
  refine (ap (fun x => x o* loop_susp_unit A) _).
  apply path_pforall.
  tapply (fmap_comp loops).
Defined.

Lemma natequiv_loop_susp_adjoint_r `{Funext} (A : pType)
  : NatEquiv (opyon (psusp A)) (opyon A o loops).
Proof.
  rapply Build_NatEquiv.
Defined.

