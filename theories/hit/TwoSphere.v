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
  apply (cancelR _ _ (concat_p_pp _ (transport_const _ b) _)^).
  apply (cancelR _ _ (whiskerL (transport2 _ surf b) (apD_const _ _)^)).
  refine ((apD02_const (S2_rec P b s) surf)^ @ _).
  refine ((S2_ind_beta_surf _ _ _) @ _).
  refine (_ @ (ap (fun w => _ @ w) 
                  (triangulator 
                     (transport2 (fun _ : S2 => P) surf b) _))). 
  cbn. refine (_ @ (ap (fun w => (w @ _) @ _) (concat_1p _)^)).
  
  refine (_ @ (concat_p_pp _ _ _)).
  refine (_ @ (ap (fun w => _ @ w) (concat_pp_p _ _ _))).
  refine (_ @ (ap (fun w => _ @ (w @ _)) (concat_Vp _)^)).
  refine (_ @ (ap (fun w => _ @ (w @ _)) 
                  (concat_pV (concat_p1 
                                (transport2 (fun _ : S2 => P) surf b @ 1))))).
  refine (_ @ (ap (fun w => _ @ w) (concat_p_pp _ _ _))).
  refine (_ @ (concat_pp_p _ _ _)). apply moveR_pV.
  refine (_ @ (concat_p_pp _ _ _)).
  refine (_ @ (ap (fun w => _ @ w) (whiskerR_p1 _)^)). f_ap.
  refine ((ap (fun w => w @ _) (whiskerL_1p_1 _)^) @ _).
  refine ((ap (fun w => _ @ w) (whiskerR_p1 _)^) @ _). cbn.
  refine ((concat_p_pp _ _ _) @ _). f_ap.
  refine ((ap (fun w => _ @ w) (concat_1p _)) @ _).
  refine ((concat_whisker 1 _ _ 1 (transport2_const surf b) s)^ @ _).
  
  symmetry.
  refine ((ap (fun w => w @@ _) (concat_p1 _)^) @ _).
  refine ((ap (fun w => _ @@ w) (concat_1p _)^) @ _).
  refine ((concat_concat2 _ _ _ _)^ @ _). f_ap.
Defined.