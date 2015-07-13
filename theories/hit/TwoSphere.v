(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the 2-sphere [S^2]. *)

Require Import HoTT.Basics HSet.
Require Import Types.Paths Types.Forall Types.Arrow Types.Universe Types.Empty Types.Unit.
Local Open Scope path_scope.

Generalizable Variables X A B f g n.

(* ** Definition of the 2-sphere. *)

Module Export TwoSphere.

Private Inductive S2 : Type0 :=
| base : S2.

Axiom surf : idpath base = idpath base.

Definition S2_ind (P : S2 -> Type) (b : P base) (s : idpath b = transport2 P surf b)
  : forall (x:S2), P x
  := fun x => match x with base => fun _ => b end s.

Axiom S2_ind_beta_surf
  : forall (P : S2 -> Type) (b : P base) (s : idpath b = transport2 P surf b),
      apD02 (S2_ind P b s) surf = s @ (concat_p1 _)^.

End TwoSphere.

(* ** The non-dependent eliminator *)

Definition S2_rec (P : Type) (b : P) (s : idpath b = idpath b)
  : S2 -> P
  := S2_ind (fun _ => P) b (s @ (transport2_const surf b) @ (concat_p1 _)).


Definition S2_rec_beta_surf (P : Type) (b : P) (s : idpath b = idpath b)
: ap02 (S2_rec P b s) surf = s.
Proof.
  apply (cancel2L (transport2_const surf b)).
  apply (cancelL (apD_const (S2_rec P b s) (idpath base))).
  apply (cancelR _ _ (concat_pp_p _ (transport_const _ b) _)).
  apply (cancelR _ _ (whiskerL (transport2 _ surf b) (apD_const _ _)^)).
  refine ((apD02_const (S2_rec P b s) surf)^ @ _).
  refine ((S2_ind_beta_surf _ _ _) @ _).
  hott_simpl. 
  apply moveL_pM. hott_simpl. apply moveR_pV. apply moveL_Mp.
  path_via (concat_pp_p (transport2 (fun _ : S2 => P) surf b) 
     (transport_const 1 b) 1).
  refine (_ @ (concat_pp_1 _ _)^). hott_simpl.
  refine (_ @ (apD concat_p1 (transport2_const _ _))). simpl.
  symmetry.
  refine (@dpath_path_FlFr _ _ (fun p : b = b => p @ 1) (fun p : b = b => p) _ _ _ _ _ _).
  refine ((concat_1p _) @ _). hott_simpl. apply moveL_pM.
  refine ((concat_pV _) @ _). apply moveL_pM. 
  refine ((concat_1p _) @ _). apply moveL_Mp.
  refine ((inv_V _)^ @ _). apply inverse2.
  refine ((inv_pp _ _) @ _). apply moveR_pV.
  refine ((inv_V _) @ _). apply moveL_Mp.
  path_via ((transport2_const surf b @@ s)^ @ (1 @@ s)).
  f_ap. refine (_ @ (concat2_1p s)^). refine (whiskerL_1p_1 _)^.
  path_via (((transport2_const surf b)^ @@ s^) @ (1 @@ s)). f_ap.
  apply concat2_V.
  refine ((concat_concat2 _ _ _ _) @ _). hott_simpl.
  refine ((concat2_p1 _) @ _). 
  path_via (whiskerR (transport2_const surf b)^ 1). f_ap. hott_simpl.
  refine (_ @ (ap_V _ (transport2_const surf b))).
  hott_simpl.
Defined.
