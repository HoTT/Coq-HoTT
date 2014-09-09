(* -*- mode: coq; mode: visual-line -*- *)

(** * The suspension of a type *)

Require Import Basics types.Paths Misc.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* ** Definition of suspension. *)

Module Export Suspension.

(** We play games to ensure that [Susp X] does not live in a lower universe than [X] *)
Section hack_my_types.
Let U := Type.
Private Inductive Susp (X : U) : U :=
  | North : Susp X
  | South : Susp X.
End hack_my_types.

Global Arguments North {X}.
Global Arguments South {X}.

Axiom merid : forall (X : Type) (x : X), North = South :> Susp X.
Global Arguments merid {X} x.

Definition Susp_rect {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
: forall (y:Susp X), P y
:= fun y => (match y return (_ -> P y)
     with North => (fun _ => H_N) | South => (fun _ => H_S) end) H_merid.

Axiom Susp_comp_merid : forall {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  (x:X),
apD (Susp_rect P H_N H_S H_merid) (merid x) = H_merid x.

End Suspension.

(* ** Non-dependent eliminator. *)

Definition Susp_rect_nd {X Y : Type}
  (H_N H_S : Y) (H_merid : X -> H_N = H_S)
: Susp X -> Y.
Proof.
  apply (Susp_rect (fun _ => Y) H_N H_S).
  intros x. exact (transport_const _ _ @ H_merid x).
Defined.

Definition Susp_comp_nd_merid {X Y : Type}
  {H_N H_S : Y} {H_merid : X -> H_N = H_S} (x:X)
: ap (Susp_rect_nd H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  apply (cancelL (transport_const (merid x) H_N)).
  transitivity (apD (Susp_rect_nd H_N H_S H_merid) (merid x)).
  symmetry; refine (apD_const (Susp_rect_nd H_N H_S H_merid) _).
  refine (Susp_comp_merid (fun _ : Susp X => Y) _ _ _ _).
Defined.

(** ** Eta-rule. *)

(** The eta-rule for suspension states that any function out of a suspension is equal to one defined by [Susp_rect] in the obvious way. We give it first in a weak form, producing just a pointwise equality, and then turn this into an actual equality using [Funext]. *)
Definition Susp_eta_homot {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f == Susp_rect P (f North) (f South) (fun x => apD f (merid x)).
Proof.
  unfold pointwise_paths. refine (Susp_rect _ 1 1 _).
  intros x.
  refine (transport_paths_FlFr_D
    (g := Susp_rect P (f North) (f South) (fun x : X => apD f (merid x)))
    _ _ @ _); simpl.
  apply moveR_pM. apply (concat (concat_p1 _)), (concatR (concat_1p _)^).
  apply ap, inverse. refine (Susp_comp_merid _ _ _ _ _).
Defined.

Definition Susp_eta `{Funext}
  {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f = Susp_rect P (f North) (f South) (fun x => apD f (merid x))
:= path_forall _ _ (Susp_eta_homot f).

(** ** Nullhomotopies of maps out of suspensions *)

Definition nullhomot_susp_from_paths {X Z: Type} (f : Susp X -> Z)
  (n : NullHomotopy (fun x => ap f (merid x)))
: NullHomotopy f.
Proof.
  exists (f North).
  refine (Susp_rect _ 1 n.1^ _); intros x.
  refine (transport_paths_Fl _ _ @ _).
  apply (concat (concat_p1 _)), ap. apply n.2.
Defined.

Definition nullhomot_paths_from_susp {X Z: Type} (H_N H_S : Z) (f : X -> H_N = H_S)
  (n : NullHomotopy (Susp_rect_nd H_N H_S f))
: NullHomotopy f.
Proof.
  exists (n.2 North @ (n.2 South)^).
  intro x. apply moveL_pV.
  transitivity (ap (Susp_rect_nd H_N H_S f) (merid x) @ n.2 South).
  apply whiskerR, inverse, Susp_comp_nd_merid.
  refine (concat_Ap n.2 (merid x) @ _).
  apply (concatR (concat_p1 _)), whiskerL. apply ap_const.
Defined.

(** ** Pointedness of [Susp] and path spaces thereof *)
(** We arbitrarily choose [North] to be the point. *)
Global Instance ispointed_susp {X : Type} : IsPointed (Susp X) | 0
  := North.

Global Instance ispointed_path_susp `{IsPointed X} : IsPointed (North = South :> Susp X) | 0
  := merid (point X).

Global Instance ispointed_path_susp' `{IsPointed X} : IsPointed (South = North :> Susp X) | 0
  := (merid (point X))^.
