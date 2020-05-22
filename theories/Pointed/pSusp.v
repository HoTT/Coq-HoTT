Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.Loops.
Require Import Pointed.pMap.
Require Import Pointed.pHomotopy.
Require Import Pointed.pTrunc.
Require Import Pointed.pEquiv.
Require Import Homotopy.Suspension.
Require Import Homotopy.Freudenthal.
Require Import Truncations.

Generalizable Variables X A B f g n.

Local Open Scope path_scope.
Local Open Scope pointed_scope.

(** ** Pointedness of [Susp] and path spaces thereof *)
(** We arbitrarily choose [North] to be the point. *)
Global Instance ispointed_susp {X : Type} : IsPointed (Susp X) | 0
  := North.

Global Instance ispointed_path_susp `{IsPointed X}
  : IsPointed (North = South :> Susp X) | 0 := merid (point X).

Global Instance ispointed_path_susp' `{IsPointed X}
  : IsPointed (South = North :> Susp X) | 0 := (merid (point X))^.

Definition psusp (X : pType) : pType
  := Build_pType (Susp X) _.

(** ** Suspension Functor *)

(* Definition of pointed suspension functor *)
Definition psusp_functor {X Y : pType} (f : X ->* Y) : psusp X ->* psusp Y
  := Build_pMap (psusp X) (psusp Y) (functor_susp f) 1.

(* Suspension functor preserves composition *)
Definition psusp_functor_compose {X Y Z : pType} (g : Y ->* Z) (f : X ->* Y)
  : psusp_functor (g o* f) ==* psusp_functor g o* psusp_functor f.
Proof.
  pointed_reduce_rewrite; srefine (Build_pHomotopy _ _); cbn.
  { srapply Susp_ind; try reflexivity; cbn.
    intros x.
    refine (transport_paths_FlFr _ _ @ _).
    rewrite concat_p1; apply moveR_Vp.
    by rewrite concat_p1, ap_compose, !Susp_rec_beta_merid. }
  reflexivity.
Qed.

(* Suspension functor preserves identity *)
Definition psusp_functor_idmap {X : pType}
  : psusp_functor (@pmap_idmap X) ==* pmap_idmap.
Proof.
  srapply Build_pHomotopy.
  { srapply Susp_ind; try reflexivity.
    intro x.
    refine (transport_paths_FFlr _ _ @ _).
    by rewrite ap_idmap, Susp_rec_beta_merid,
      concat_p1, concat_Vp. }
  reflexivity.
Qed.

Definition psusp_2functor {X Y} {f g : X ->* Y} (p : f ==* g)
  : psusp_functor f ==* psusp_functor g.
Proof.
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
Defined.

Definition pequiv_psusp_functor {X Y : pType} (f : X <~>* Y)
  : psusp X <~>* psusp Y.
Proof.
  srapply pequiv_adjointify.
  1: apply psusp_functor, f.
  1: apply psusp_functor, f^-1*.
  1,2: refine ((psusp_functor_compose _ _)^* @* _ @* psusp_functor_idmap).
  1,2: apply psusp_2functor.
  1: apply peisretr.
  apply peissect.
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
    transitivity {bp : {b:B & point B = b} & {f : A -> point B = bp.1 & f (point A) = bp.2} }.
    1:make_equiv.
    refine (_ oE equiv_contr_sigma _); simpl.
    refine (issig_pmap A (loops B)).
  Defined.

  (** Unfortunately, with this definition it seems to be quite hard to prove that the isomorphism is natural on pointed maps.  The following proof gets partway there, but ends with a pretty intractable goal.  It's also quite slow, so we don't want to compile it all the time. *)
  (**
<<
  Definition loop_susp_adjoint_nat_r `{Funext} (A B B' : pType)
             (f : psusp A ->* B) (g : B ->* B')
  : loop_susp_adjoint A B' (g o* f)
    ==* loops_functor g o* loop_susp_adjoint A B f.
  Proof.
    pointed_reduce_rewrite.
    srefine (Build_pHomotopy _ _).
    - intros a. simpl.
      refine (_ @ (concat_1p _)^).
      refine (_ @ (concat_p1 _)^).
      rewrite !transport_sigma. simpl.
      rewrite !(transport_arrow_fromconst (B := A)).
      rewrite !transport_paths_Fr.
      rewrite !ap_V, !ap_pr1_path_basedpaths.
      rewrite ap_pp, !(ap_compose f g), ap_V.
      reflexivity.
    - cbn.
      Fail reflexivity.
  Abort.
>>
   *)

End Book_Loop_Susp_Adjunction.

(** Thus, instead we will construct the adjunction in terms of a unit and counit natural transformation. *)

Definition loop_susp_unit (X : pType) : X ->* loops (psusp X)
  := Build_pMap X (loops (psusp X))
      (fun x => merid x @ (merid (point X))^) (concat_pV _).

(** By Freudenthal, we have that this map is 2n-connected for a n-connected X *)
Instance conn_map_loop_susp_unit `{Univalence} (X : pType) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (fun x => merid x @ (merid (point X))^).
Proof.
  refine (conn_map_compose _ _ (equiv_concat_r (merid (point _))^ _)).
Defined.

(** We also have this corollary *)
Lemma pequiv_ptr_loop_psusp `{Univalence} (X : pType) n `{IsConnected n.+1 X}
  : pTr (n +2+ n) X <~>* pTr (n +2+ n) (loops (psusp X)).
Proof.
  snrefine (Build_pEquiv _ _ _ (isequiv_conn_map_ino (n +2+ n) _)).
  { apply ptr_functor.
    apply loop_susp_unit. }
  all:exact _.
Defined.

Definition loop_susp_unit_natural {X Y : pType} (f : X ->* Y)
  : loop_susp_unit Y o* f
  ==* loops_functor (psusp_functor f) o* loop_susp_unit X.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; symmetry.
    refine (concat_1p _@ (concat_p1 _ @ _)).
    refine (ap_pp (Susp_rec North South (merid o f))
                  (merid x) (merid (point X))^ @ _).
    refine ((1 @@ ap_V _ _) @ _).
    refine (Susp_rec_beta_merid _ @@ inverse2 (Susp_rec_beta_merid _)).
  - cbn. apply moveL_pV. rewrite !inv_pp, !concat_pp_p, concat_1p; symmetry.
    apply moveL_Vp.
    refine (concat_pV_inverse2 _ _ (Susp_rec_beta_merid (point X)) @ _).
    apply moveL_Vp, moveL_Vp.
    refine (ap_pp_concat_pV _ _ @ _).
    apply moveL_Vp, moveL_Vp.
    rewrite concat_p1_1, concat_1p_1.
    cbn; symmetry.
    refine (concat_p1 _ @ _).
    refine (ap_compose
      (fun p' => (ap (Susp_rec North South (merid o f))) p' @ 1)
      (fun p' => 1 @ p')
      (concat_pV (merid (point X))) @ _).
    apply ap.
    refine (ap_compose (ap (Susp_rec North South (merid o f)))
      (fun p' => p' @ 1) _).
Qed.

Definition loop_susp_counit (X : pType) : psusp (loops X) ->* X
  :=  Build_pMap (psusp (loops X)) X (Susp_rec (point X) (point X) idmap) 1.

Definition loop_susp_counit_natural {X Y : pType} (f : X ->* Y)
  : f o* loop_susp_counit X
  ==* loop_susp_counit Y o* psusp_functor (loops_functor f).
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
    refine (Susp_rec_beta_merid _). 
  - reflexivity.
Qed.

(** Now the triangle identities *)

Definition loop_susp_triangle1 (X : pType)
  : loops_functor (loop_susp_counit X) o* loop_susp_unit (loops X)
  ==* pmap_idmap.
Proof.
  simple refine (Build_pHomotopy _ _).
  - intros p; cbn.
    refine (concat_1p _ @ (concat_p1 _ @ _)).
    refine (ap_pp (Susp_rec (point X) (point X) idmap)
                  (merid p) (merid (point (point X = point X)))^ @ _).
    refine ((1 @@ ap_V _ _) @ _).
    refine ((Susp_rec_beta_merid p
      @@ inverse2 (Susp_rec_beta_merid (point (loops X)))) @ _).
    exact (concat_p1 _).
  - apply moveL_pV. destruct X as [X x]; cbn; unfold point.
    apply whiskerR.
    rewrite (concat_pV_inverse2
               (ap (Susp_rec x x idmap) (merid 1))
               1 (Susp_rec_beta_merid 1)).
    rewrite (ap_pp_concat_pV (Susp_rec x x idmap) (merid 1)).
    rewrite ap_compose, (ap_compose _ (fun p => p @ 1)).
    rewrite concat_1p_1; apply ap.
    apply concat_p1_1.
Qed.

Definition loop_susp_triangle2 (X : pType)
  : loop_susp_counit (psusp X) o* psusp_functor (loop_susp_unit X)
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
  : (psusp A ->* B) <~> (A ->* loops B).
Proof.
  refine (equiv_adjointify
            (fun f => loops_functor f o* loop_susp_unit A)
            (fun g => loop_susp_counit B o* psusp_functor g) _ _).
  - intros g. apply path_pforall.
    refine (pmap_prewhisker _ (loops_functor_compose _ _) @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker _ (loop_susp_unit_natural g)^* @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker g (loop_susp_triangle1 B) @* _).
    apply pmap_postcompose_idmap.
  - intros f. apply path_pforall.
    refine (pmap_postwhisker _ (psusp_functor_compose _ _) @* _).
    refine ((pmap_compose_assoc _ _ _)^* @* _).
    refine (pmap_prewhisker _ (loop_susp_counit_natural f)^* @* _).
    refine (pmap_compose_assoc _ _ _ @* _).
    refine (pmap_postwhisker f (loop_susp_triangle2 A) @* _).
    apply pmap_precompose_idmap.
Defined.

(** And its naturality is easy. *)

Definition loop_susp_adjoint_nat_r `{Funext} (A B B' : pType)
  (f : psusp A ->* B) (g : B ->* B') : loop_susp_adjoint A B' (g o* f)
  ==* loops_functor g o* loop_susp_adjoint A B f.
Proof.
  cbn.
  refine (_ @* pmap_compose_assoc _ _ _).
  apply pmap_prewhisker.
  refine (loops_functor_compose g f).
Defined.

Definition loop_susp_adjoint_nat_l `{Funext} (A A' B : pType)
  (f : A ->* loops B) (g : A' ->* A) : (loop_susp_adjoint A' B)^-1 (f o* g)
  ==* (loop_susp_adjoint A B)^-1 f o* psusp_functor g.
Proof.
  cbn.
  refine (_ @* (pmap_compose_assoc _ _ _)^*).
  apply pmap_postwhisker.
  refine (psusp_functor_compose f g).
Defined.
