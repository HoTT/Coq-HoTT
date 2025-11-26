From HoTT Require Import Basics Types.
Require Import WildCat.Equiv.
Require Import Homotopy.NullHomotopy.
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

(** ** Pointed sphere for non-negative dimensions. *)
Definition psphere (n : nat) : pType := [Sphere n, _].

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

Instance isequiv_S0_to_Bool : IsEquiv (S0_to_Bool) | 0.
Proof.
  apply isequiv_adjointify with Bool_to_S0.
  - intros [ | ]; exact 1.
  - refine (Susp_ind _ 1 1 _). intros [].
Defined.

Definition equiv_S0_Bool : Sphere 0 <~> Bool
  := Build_Equiv _ _ _ isequiv_S0_to_Bool.

Definition ispointed_bool : IsPointed Bool := true.

Definition pBool := [Bool, true].

Definition pequiv_S0_Bool : psphere 0 <~>* pBool
  := @Build_pEquiv' (psphere 0) pBool equiv_S0_Bool 1.

(** In [pmap_from_psphere_iterated_loops] below, we'll use this universal property of [pBool]. *)
Definition pmap_from_bool `{Funext} (X : pType)
  : (pBool ->** X) <~>* X.
Proof.
  snapply Build_pEquiv'.
  - refine (_ oE (issig_pmap _ _)^-1%equiv).
    refine (_ oE (equiv_functor_sigma_pb (equiv_bool_rec_uncurried X))^-1%equiv); cbn.
    make_equiv_contr_basedpaths.
  - reflexivity.
Defined.

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

Instance isequiv_S1_to_Circle : IsEquiv (S1_to_Circle) | 0.
Proof.
  apply isequiv_adjointify with Circle_to_S1.
  - refine (Circle_ind _ 1 _).
    transport_paths FFlr; apply equiv_p1_1q.
    refine (ap _ (Circle_rec_beta_loop _ _ _) @ _).
    lhs napply Susp_rec_beta_zigzag.
    simpl.
    apply concat_p1.
  - snapply Susp_ind_FFlr; simpl.
    1: reflexivity.
    1: exact (merid South).
    intro x.
    unfold S1_to_Circle; rewrite (Susp_rec_beta_merid x).
    revert x. change (Susp Empty) with (Sphere 0).
    apply (equiv_ind (S0_to_Bool ^-1)); intros x.
    case x; simpl.
    2: reflexivity.
    rhs napply concat_1p.
    unfold Circle_to_S1; rewrite Circle_rec_beta_loop.
    apply concat_pV_p.
Defined.

Definition equiv_S1_Circle : Sphere 1 <~> Circle
  := Build_Equiv _ _ _ isequiv_S1_to_Circle.

Definition pequiv_S1_Circle : psphere 1 <~>* [Circle, _].
Proof.
  srapply Build_pEquiv'.
  1: exact equiv_S1_Circle.
  reflexivity.
Defined.

(** *** [Sphere 2] *)
Definition S2_to_TwoSphere : (Sphere 2) -> TwoSphere.
Proof.
  apply (Susp_rec base base).
  apply (Susp_rec (idpath base) (idpath base)).
  apply (Susp_rec surf (idpath (idpath base))).
  exact Empty_rec.
Defined.

Definition TwoSphere_to_S2 : TwoSphere -> (Sphere 2).
Proof.
  apply (TwoSphere_rec (Sphere 2) North).
  refine (transport (fun x => x = x) (concat_pV (merid North)) _).
  exact (((ap (fun u => merid u @ (merid North)^) 
               (merid North @ (merid South)^)))).
Defined.

Definition issect_TwoSphere_to_S2 : S2_to_TwoSphere o TwoSphere_to_S2 == idmap.
Proof.
  refine (TwoSphere_ind _ 1 _). 
  rhs_V rapply concat_p1.
  rhs exact (@concat_Ap (base = base) _ _
                          (fun p => (p^ @ ap S2_to_TwoSphere (ap TwoSphere_to_S2 p))^)
                          (fun x =>
                             (transport_paths_FFlr x 1) 
                               @ ap (fun u => u @ x) (concat_p1 _)
                               @ ap (fun w => _ @ w) (inv_V x)^ 
                               @ (inv_pp _ _)^) 
                          1 1 surf).
  rhs rapply concat_1p.
  rhs exact (ap_compose (fun p => p^ @ ap S2_to_TwoSphere (ap TwoSphere_to_S2 p))
                          inverse
                          surf).
  refine (@ap _ _ (ap inverse) 1 _ _).
  rhs_V rapply concat2_ap_ap.
  rhs exact (ap (fun w => inverse2 surf @@ w)
                  (ap_compose (ap TwoSphere_to_S2) (ap S2_to_TwoSphere) surf)).
  lhs_V exact (concat_Vp_inverse2 _ _ surf).
  lhs rapply concat_p1.
  refine (ap (fun p : 1 = 1 => inverse2 surf @@ p) _).

  symmetry. lhs refine ((ap (ap (ap S2_to_TwoSphere))
                        (TwoSphere_rec_beta_surf (Sphere 2) North _))).
  lhs refine (ap_transport (concat_pV (merid North))
                        (fun z => @ap _ _ _ z z) 
                        (ap (fun u => merid u @ (merid North)^)
                            (merid North @ (merid South)^))).
  
  lhs_V exact (ap (transport (fun z => ap S2_to_TwoSphere z = ap S2_to_TwoSphere z)
                      (concat_pV (merid North)))
               (ap_compose (fun u => merid u @ (merid North)^) (ap S2_to_TwoSphere)
                           (merid North @ (merid South)^))).
  transport_paths FlFr; symmetry.
  lhs_V refine (1 @@ ap_ap_concat_pV _ _ _ (Susp_rec_beta_merid North)).
  simpl.
  lhs exact (concat_Ap (fun x => ap_pV S2_to_TwoSphere (merid x) (merid North)
                                  @ ((Susp_rec_beta_merid x
                                        @@ inverse2 (Susp_rec_beta_merid North))
                                       @ 1))
               (merid North @ (merid South)^)).
  f_ap.
  1: exact (ap_ap_concat_pV _ _ _ (Susp_rec_beta_merid North)).
  lhs_V exact (concat2_ap_ap (Susp_rec 1 1 (Susp_rec surf 1 Empty_rec))
                         (fun _ => 1)
                         (merid North @ (merid South)^)).
  lhs nrefine (ap (fun w => _ @@ w) (ap_const _ _)).
  lhs napply whiskerR_p1_1.
  rhs_V napply concat_p1.
  napply Susp_rec_beta_zigzag.
Defined. (* A bit slow, ~0.2s. *)

Definition issect_S2_to_TwoSphere : TwoSphere_to_S2 o S2_to_TwoSphere == idmap.
Proof.
  intro x.
  refine ((Susp_rec_eta_homotopic (TwoSphere_to_S2 o S2_to_TwoSphere) x) @ _). symmetry.
  generalize dependent x.
  refine (Susp_ind _ 1 (merid North)^ _).
  intro x.
  refine ((transport_paths_FlFr (f := fun y => y) _ _) @ _).
  rewrite_moveR_Vp_p. refine ((concat_1p _) @ _).
  refine (_ @ (ap (fun w => w @ _) (ap_idmap _)^)).
  refine ((Susp_rec_beta_merid _) @ _).
  path_via (ap TwoSphere_to_S2 (ap S2_to_TwoSphere (merid x))).
  { exact (ap_compose S2_to_TwoSphere TwoSphere_to_S2 (merid x)). }
  path_via (ap TwoSphere_to_S2 
               (Susp_rec 1 1 (Susp_rec surf 1 Empty_rec) x)). 
  { repeat f_ap. apply Susp_rec_beta_merid. }
  symmetry. generalize dependent x. 

  simple refine (Susp_ind _ (concat_pV (merid North)) _ _).
  - refine (_ @ (concat_pV (merid North))). 
    exact (ap (fun w => merid w @ (merid North)^) (merid South)^).
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
    + exact (TwoSphere_rec_beta_surf _ _ _).
    + refine (_ @ (ap (fun w => transport _ _ (ap _ w))
                      (concat_pV (merid South))^)).
      refine (_ @ (transport_paths_lr _ _)^).
      refine (_ @ (ap (fun w => w @ _) (concat_p1 _)^)).
      refine (concat_Vp _)^.
    + apply Empty_ind.
Defined.

Instance isequiv_S2_to_TwoSphere : IsEquiv (S2_to_TwoSphere) | 0.
Proof.
  apply isequiv_adjointify with TwoSphere_to_S2.
  - exact issect_TwoSphere_to_S2.
  - exact issect_S2_to_TwoSphere.
Defined.

Definition equiv_S2_TwoSphere : Sphere 2 <~> TwoSphere
  := Build_Equiv _ _ _ isequiv_S2_to_TwoSphere.

(** ** Truncation and connectedness of spheres. *)

(** S0 is 0-truncated. *)
Instance istrunc_s0 : IsHSet (Sphere 0).
Proof.
  exact (istrunc_isequiv_istrunc _ S0_to_Bool^-1).
Defined.

(** S1 is 1-truncated. *)
Instance istrunc_s1 `{Univalence} : IsTrunc 1 (Sphere 1).
Proof.
  srapply (istrunc_isequiv_istrunc _ S1_to_Circle^-1).
Defined.

Instance isconnected_sn n : IsConnected n.+1 (Sphere n.+2).
Proof.
  induction n.
  { srapply contr_inhabited_hprop.
    apply tr, North. }
  exact isconnected_susp.
Defined.

(** ** Truncatedness via spheres  *)

(** We show here that a type is n-truncated if and only if every map from the (n+1)-sphere into it is null-homotopic.  (One direction of this is of course the assertion that the (n+1)-sphere is n-connected.) *)

(** TODO: re-type these lemmas in terms of truncation. *)

Fixpoint allnullhomot_trunc {n : trunc_index} {X : Type} `{IsTrunc n X}
  (f : Sphere n.+1 -> X) {struct n}
: NullHomotopy f.
Proof.
  destruct n as [ | n'].
  - exists (center X). intros [].
  - apply nullhomot_susp_from_paths.
    rapply allnullhomot_trunc.
Defined.

Fixpoint istrunc_allnullhomot {n : trunc_index} {X : Type}
  (HX : forall (f : Sphere n.+2 -> X), NullHomotopy f) {struct n}
: IsTrunc n.+1 X.
Proof.
  destruct n as [ | n'].
  - (* n = -2 *) apply hprop_allpath.
    intros x0 x1. set (f := (fun b => if (S0_to_Bool b) then x0 else x1)).
    set (n := HX f). exact (n.2 North @ (n.2 South)^).
  - (* n ≥ -1 *) apply istrunc_S; intros x0 x1.
    apply (istrunc_allnullhomot n').
    intro f. apply nullhomot_paths_from_susp, HX.
Defined.

(** Iterated loop spaces can be described using pointed maps from spheres.  The [n = 0] case of this is stated using [Bool] in [pmap_from_bool] above, and the [n = 1] case of this is stated using [Circle] in [pmap_from_circle_loops] in Circle.v. *)
Definition pmap_from_psphere_iterated_loops `{Funext} (n : nat) (X : pType)
  : (psphere n ->** X) <~>* iterated_loops n X.
Proof.
  induction n as [|n IHn]; simpl.
  - exact (pmap_from_bool X o*E pequiv_pequiv_precompose pequiv_S0_Bool^-1* ).
  - refine (emap loops IHn o*E _).
    refine (_ o*E loop_susp_adjoint (psphere n) _).
    symmetry; apply equiv_loops_ppforall.
Defined.
