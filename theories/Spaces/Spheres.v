(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Import HProp NullHomotopy.
Require Import Homotopy.Suspension.
Require Import Pointed.
Require Import Truncations.
Require Import Spaces.Circle Spaces.TwoSphere.

(** * The spheres, in all dimensions. *)

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope path_scope.

Generalizable Variables X A B f g n.

(** ** Definition, by iterated suspension. *)

(** To match the usual indexing for spheres, we have to pad the sequence with a dummy term [Sphere -2]. *)
Fixpoint Sphere (n : trunc_index)
  := match n return Type with
       | -2 => Empty
       | -1 => Empty
       | n'.+1 => Susp (Sphere n')
     end.

(** ** Pointed sphere for non-negative dimensions *)
Fixpoint psphere (n : nat) : pType
  := match n with
      | O => Build_pType (Susp Empty) North
      | S n' => psusp (psphere n')
     end.

Arguments Sphere : simpl never.
Arguments psphere : simpl never.

(** ** Explicit equivalences in low dimensions  *)

(** *** [Sphere 0] *)
Definition S0_to_Bool : (Sphere 0) -> Bool.
Proof.
  simpl. apply (Susp_rec true false). intros [].
Defined.

Definition Bool_to_S0 : Bool -> (Sphere 0).
Proof.
  exact (fun b => if b then North else South).
Defined.

Global Instance isequiv_S0_to_Bool : IsEquiv (S0_to_Bool) | 0.
Proof.
  apply isequiv_adjointify with Bool_to_S0.
  - intros [ | ]; exact 1.
  - unfold Sect. refine (Susp_ind _ 1 1 _). intros [].
Defined.

Definition equiv_S0_Bool : Sphere 0 <~> Bool
  := Build_Equiv _ _ _ isequiv_S0_to_Bool.

(** *** [Sphere 1] *)
Definition S1_to_Circle : (Sphere 1) -> Circle.
Proof.
  apply (Susp_rec Circle.base Circle.base).
  exact (fun x => if (S0_to_Bool x) then loop else 1).
Defined.

Definition Circle_to_S1 : Circle -> (Sphere 1).
Proof.
  apply (Circle_rec _ North).
  exact (merid North @ (merid South)^).
Defined.

Global Instance isequiv_S1_to_Circle : IsEquiv (S1_to_Circle) | 0.
Proof.
  apply isequiv_adjointify with Circle_to_S1.
  - refine (Circle_ind _ 1 _).
    refine ((transport_paths_FFlr _ _) @ _).
    unfold Circle_to_S1; rewrite Circle_rec_beta_loop.
    rewrite ap_pp, ap_V.
    unfold S1_to_Circle. simpl. rewrite 2 Susp_rec_beta_merid. simpl.
    hott_simpl.
  - refine (Susp_ind (fun x => Circle_to_S1 (S1_to_Circle x) = x)
                     1 (merid South) _); intros x.
    refine ((transport_paths_FFlr _ _) @ _).
    unfold S1_to_Circle; rewrite (Susp_rec_beta_merid x).
    revert x. change (Susp Empty) with (Sphere 0).
    apply (equiv_ind (S0_to_Bool ^-1)); intros x.
    case x; simpl.
    2: apply concat_1p.
    unfold Circle_to_S1; rewrite Circle_rec_beta_loop.
    refine (whiskerR (concat_p1 _) _ @ _).
    apply moveR_Vp. hott_simpl.
Defined.

Definition equiv_S1_Circle : Sphere 1 <~> Circle
  := Build_Equiv _ _ _ isequiv_S1_to_Circle.

Definition pequiv_S1_Circle : psphere 1 <~>* (Build_pType Circle _).
Proof.
  srapply Build_pEquiv'.
  1: apply equiv_S1_Circle.
  reflexivity.
Defined.

(** *** [Sphere 2] *)
Definition S2_to_TwoSphere : (Sphere 2) -> TwoSphere.
Proof.
  apply (Susp_rec base base).
  apply (Susp_rec (idpath base) (idpath base)).
  apply (Susp_rec surf (idpath (idpath base))).
  apply Empty_rec.
Defined.

Definition TwoSphere_to_S2 : TwoSphere -> (Sphere 2).
Proof.
  apply (TwoSphere_rec (Sphere 2) North).
  refine (transport (fun x => x = x) (concat_pV (merid North)) _).
  refine (((ap (fun u => merid u @ (merid North)^) 
               (merid North @ (merid South)^)))).
Defined.

Definition issect_TwoSphere_to_S2 : Sect TwoSphere_to_S2 S2_to_TwoSphere.
Proof.
  refine (TwoSphere_ind _ 1 _). 
  refine (_ @ (concat_p1 _)).
  refine (_ @ (@concat_Ap (base = base) _ _
                          (fun p => (p^ @ ap S2_to_TwoSphere (ap TwoSphere_to_S2 p))^)
                          (fun x =>
                             (transport_paths_FFlr x 1) 
                               @ ap (fun u => u @ x) (concat_p1 _)
                               @ ap (fun w => _ @ w) (inv_V x)^ 
                               @ (inv_pp _ _)^) 
                          1 1 surf)^).
  refine (_ @ (concat_1p _)^).
  refine (_ @ (ap_compose (fun p => p^ @ ap S2_to_TwoSphere (ap TwoSphere_to_S2 p)) 
                          inverse
                          surf)^).
  refine (@ap _ _ (ap inverse) 1 _ _).
  refine (_ @ (concat2_ap_ap _ _ _)).
  refine (_ @ (ap (fun w => inverse2 surf @@ w) 
                  (ap_compose (ap TwoSphere_to_S2) (ap S2_to_TwoSphere) surf))^).
  refine ((concat_Vp_inverse2 _ _ surf)^ @ _).
  refine ((concat_p1 _) @ _). 
  refine (ap (fun p : 1 = 1 => inverse2 surf @@ p) _).

  symmetry. refine ((ap (ap (ap S2_to_TwoSphere))
                        (TwoSphere_rec_beta_surf (Sphere 2) North _)) @ _).
  refine ((ap_transport (concat_pV (merid North))
                        (fun z => @ap _ _ _ z z) 
                        (ap (fun u => merid u @ (merid North)^)
                            (merid North @ (merid South)^))) @ _).
  
  refine ((ap (transport (fun z => ap S2_to_TwoSphere z = ap S2_to_TwoSphere z) 
                         (concat_pV (merid North)))
              (ap_compose (fun u => merid u @ (merid North)^) (ap S2_to_TwoSphere) 
                          (merid North @ (merid South)^))^) @ _).
  refine ((transport_paths_FlFr _ _) @ _). rewrite_moveR_Vp_p.
  refine ((ap (fun w => _ @ w) 
              (ap_pp_concat_pV S2_to_TwoSphere (merid North))^) @ _).
  refine ((ap (fun w => _ @ (_ @ (_ @ w)))
              (concat_pV_inverse2 (ap S2_to_TwoSphere (merid North)) 
                                  _ 
                                  (Susp_rec_beta_merid North))^) @ _).
  refine ((@concat_Ap (Sphere 1) _ 
                      (fun x => ap S2_to_TwoSphere (merid x @ (merid North)^))
                      (fun x => Susp_rec 1 1 
                                (Susp_rec surf 1 
                                Empty_rec) x 
                                @ 1)
                      (fun x => ap_pp S2_to_TwoSphere (merid x) (merid North)^ 
                                @ ((1 @@ ap_V S2_to_TwoSphere (merid North)) 
                                @ ((Susp_rec_beta_merid x 
                                   @@ inverse2 (Susp_rec_beta_merid North)) 
                                @ 1)))
                      North North (merid North @ (merid South)^)) @ _). f_ap.
  { refine (_ @ (ap_pp_concat_pV _ _)).
    refine (ap (fun w => _ @ (_ @ w)) (concat_pV_inverse2 _ _ _)). }
  refine ((concat2_ap_ap (Susp_rec 1 1 (Susp_rec surf 1 
                                         Empty_rec)) 
                         (fun _ => 1) 
                         (merid North @ (merid South)^))^ @ _).
  refine ((ap (fun w => _ @@ w) (ap_const _ _)) @ _).
  refine ((concat2_p1 _) @ _). refine ((whiskerR_p1_1 _) @ _).
  refine ((ap_pp _ (merid North) (merid South)^) @ _). 
  refine (_ @ (concat_p1 _)). f_ap.
  - refine (Susp_rec_beta_merid North).
  - refine (ap_V _ _ @ _). refine (@inverse2 _ _ _ _ 1 _).
    refine (Susp_rec_beta_merid South).
Defined.

Definition issect_S2_to_TwoSphere : Sect S2_to_TwoSphere TwoSphere_to_S2.
Proof.
  intro x.
  refine ((Susp_rec_eta_homot (TwoSphere_to_S2 o S2_to_TwoSphere) x) @ _). symmetry.
  generalize dependent x.
  refine (Susp_ind _ 1 (merid North)^ _).
  intro x.
  refine ((transport_paths_FlFr (f := fun y => y) _ _) @ _).
  rewrite_moveR_Vp_p. refine ((concat_1p _) @ _).
  refine (_ @ (ap (fun w => w @ _) (ap_idmap _)^)).
  refine ((Susp_rec_beta_merid _) @ _).
  path_via (ap TwoSphere_to_S2 (ap S2_to_TwoSphere (merid x))).
  { apply (ap_compose S2_to_TwoSphere TwoSphere_to_S2 (merid x)). }
  path_via (ap TwoSphere_to_S2 
               (Susp_rec 1 1 (Susp_rec surf 1 Empty_rec) x)). 
  { repeat f_ap. apply Susp_rec_beta_merid. }
  symmetry. generalize dependent x. 

  simple refine (Susp_ind _ (concat_pV (merid North)) _ _).
  - refine (_ @ (concat_pV (merid North))). 
    apply (ap (fun w => merid w @ (merid North)^) (merid South)^).
  - intro x.
    refine ((transport_paths_FlFr (merid x) (concat_pV (merid North))) @ _).
    rewrite_moveR_Vp_p. symmetry. refine ((dpath_path_lr _ _ _)^-1 _).
    refine ((ap (transport _ _) (ap_pp _ (merid x) (merid South)^)^) @ _).
    refine (_ @ (ap_compose (Susp_rec 1 1 
                              (Susp_rec surf 1 
                                Empty_rec)) 
                            (ap TwoSphere_to_S2) (merid x))^).
    refine (_ @ (ap (ap02 TwoSphere_to_S2) (Susp_rec_beta_merid _)^)).
    symmetry. generalize dependent x.
    
    simple refine (Susp_ind _ _ _ _).
    + refine (TwoSphere_rec_beta_surf _ _ _).
    + refine (_ @ (ap (fun w => transport _ _ (ap _ w))
                      (concat_pV (merid South))^)).
      refine (_ @ (transport_paths_lr _ _)^).
      refine (_ @ (ap (fun w => w @ _) (concat_p1 _)^)).
      refine (concat_Vp _)^.
    + apply Empty_ind.
Defined.

Global Instance isequiv_S2_to_TwoSphere : IsEquiv (S2_to_TwoSphere) | 0.
Proof.
  apply isequiv_adjointify with TwoSphere_to_S2.
  - apply issect_TwoSphere_to_S2.
  - apply issect_S2_to_TwoSphere.
Defined.

Definition equiv_S2_TwoSphere : Sphere 2 <~> TwoSphere
  := Build_Equiv _ _ _ isequiv_S2_to_TwoSphere.

(** ** Truncation and connectedness of spheres. *)

(** S0 is 0-truncated. *)
Global Instance istrunc_s0 : IsHSet (Sphere 0).
Proof.
  srapply (trunc_equiv _ S0_to_Bool^-1).
Defined.

(** S1 is 1-truncated. *)
Global Instance istrunc_s1 `{Univalence} : IsTrunc 1 (Sphere 1).
Proof.
  srapply (trunc_equiv _ S1_to_Circle^-1).
Defined.

Global Instance isconnected_sn n : IsConnected n.+1 (Sphere n.+2).
Proof.
  induction n.
  { srapply contr_inhabited_hprop.
    apply tr, North. }
  apply isconnected_susp.
Defined.

(** ** Truncatedness via spheres  *)

(** We show here that a type is n-truncated if and only if every map from the (n+1)-sphere into it is null-homotopic.  (One direction of this is of course the assertion that the (n+1)-sphere is n-connected.) *)

(** TODO: re-type these lemmas in terms of truncation. *)

Fixpoint allnullhomot_trunc {n : trunc_index} {X : Type} `{IsTrunc n X}
  (f : Sphere n.+1 -> X) {struct n}
: NullHomotopy f.
Proof.
  destruct n as [ | n'].
  - simpl in *. exists (center X). intros [ ].
  - apply nullhomot_susp_from_paths.
    apply allnullhomot_trunc; auto with typeclass_instances.
Defined.

Fixpoint trunc_allnullhomot {n : trunc_index} {X : Type}
  (HX : forall (f : Sphere n.+2 -> X), NullHomotopy f) {struct n}
: IsTrunc n.+1 X.
Proof.
  destruct n as [ | n'].
  - (* n = -2 *) apply hprop_allpath.
    intros x0 x1. set (f := (fun b => if (S0_to_Bool b) then x0 else x1)).
    set (n := HX f). exact (n.2 North @ (n.2 South)^).
  - (* n ≥ -1 *) intros x0 x1.
    apply (trunc_allnullhomot n').
    intro f. apply nullhomot_paths_from_susp, HX.
Defined.
