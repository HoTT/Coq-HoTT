(* -*- mode: coq; mode: visual-line -*- *)

(** * The suspension of a type *)

Require Import Basics Types.
Require Import HIT.Pushout.
Require Import NullHomotopy.
Local Open Scope path_scope.

Generalizable Variables X A B f g n.

(* ** Definition of suspension *)

Definition Susp (X : Type) := pushout (@const X _ tt) (const tt).
Definition North {X} : Susp X := pushl tt.
Definition South {X} : Susp X := pushr tt.
Definition merid {X} (x : X) : North = South := pp x.

Definition Susp_ind {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  : forall (y : Susp X), P y.
Proof.
  serapply pushout_ind.
  - exact (Unit_ind H_N).
  - exact (Unit_ind H_S).
  - exact (H_merid).
Defined.

Definition Susp_ind_beta_merid {X : Type}
  (P : Susp X -> Type) (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S) (x : X)
  : apD (Susp_ind P H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  serapply pushout_ind_beta_pp.
Defined.

(** We want to allow the user to forget that we've defined suspension
    in this way. *)
Arguments Susp : simpl never.
Arguments North : simpl never.
Arguments South : simpl never.
Arguments merid : simpl never.
Arguments Susp_ind_beta_merid : simpl never.

(* ** Non-dependent eliminator. *)

Definition Susp_rec {X Y : Type}
  (H_N H_S : Y) (H_merid : X -> H_N = H_S)
: Susp X -> Y.
Proof.
  apply (Susp_ind (fun _ => Y) H_N H_S).
  intros x. exact (transport_const _ _ @ H_merid x).
Defined.

Global Arguments Susp_rec {X Y}%type_scope H_N H_S H_merid%function_scope _.

Definition Susp_rec_beta_merid {X Y : Type}
  {H_N H_S : Y} {H_merid : X -> H_N = H_S} (x:X)
: ap (Susp_rec H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  apply (cancelL (transport_const (merid x) H_N)).
  transitivity (apD (Susp_rec H_N H_S H_merid) (merid x)).
  - symmetry; refine (apD_const (Susp_rec H_N H_S H_merid) _).
  - refine (Susp_ind_beta_merid (fun _ : Susp X => Y) _ _ _ _).
Defined.

(** ** Eta-rule. *)

(** The eta-rule for suspension states that any function out of a suspension is equal to one defined by [Susp_ind] in the obvious way. We give it first in a weak form, producing just a pointwise equality, and then turn this into an actual equality using [Funext]. *)
Definition Susp_eta_homot {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f == Susp_ind P (f North) (f South) (fun x => apD f (merid x)).
Proof.
  unfold pointwise_paths. refine (Susp_ind _ 1 1 _).
  intros x.
  refine (transport_paths_FlFr_D
    (g := Susp_ind P (f North) (f South) (fun x : X => apD f (merid x)))
    _ _ @ _); simpl.
  apply moveR_pM. apply (concat (concat_p1 _)), (concatR (concat_1p _)^).
  apply ap, inverse. refine (Susp_ind_beta_merid _ _ _ _ _).
Defined.

Definition Susp_rec_eta_homot {X Y : Type} (f : Susp X -> Y)
: f == Susp_rec (f North) (f South) (fun x => ap f (merid x)).
Proof.
  refine (Susp_ind _ 1 1 _).
  intro x.
  refine ((transport_paths_FlFr _ _) @ _). apply moveR_Mp.
  refine ((Susp_rec_beta_merid _) @ _). hott_simpl.
  refine (_ @ (ap_V f _)). f_ap.
  refine (inv_V _)^.
Defined.  

Definition Susp_eta `{Funext}
  {X : Type} {P : Susp X -> Type} (f : forall y, P y)
  : f = Susp_ind P (f North) (f South) (fun x => apD f (merid x))
:= path_forall _ _ (Susp_eta_homot f).

Definition Susp_rec_eta `{Funext} {X Y : Type} (f : Susp X -> Y)
  : f = Susp_rec (f North) (f South) (fun x => ap f (merid x))
:= path_forall _ _ (Susp_rec_eta_homot f).

(** ** Universal property *)

Definition equiv_Susp_rec `{Funext} (X Y : Type)
: (Susp X -> Y) <~> { NS : Y * Y & X -> fst NS = snd NS }.
Proof.
  simple refine (BuildEquiv (Susp X -> Y)
                     { NS : Y * Y & X -> fst NS = snd NS } _ _).
  { intros f.
    exists (f North , f South).
    intros x. exact (ap f (merid x)). }
  simple refine (isequiv_adjointify _ _ _ _).
  - intros [[N S] m].
    exact (Susp_rec N S m).
  - intros [[N S] m].
    apply ap, path_arrow. intros x; apply Susp_rec_beta_merid.
  - intros f.
    symmetry.
    refine (Susp_eta f @ _).
    unfold Susp_rec; apply ap.
    apply path_forall; intros x.
    apply apD_const.
Defined.

(** ** Nullhomotopies of maps out of suspensions *)

Definition nullhomot_susp_from_paths {X Z: Type} (f : Susp X -> Z)
  (n : NullHomotopy (fun x => ap f (merid x)))
: NullHomotopy f.
Proof.
  exists (f North).
  refine (Susp_ind _ 1 n.1^ _); intros x.
  refine (transport_paths_Fl _ _ @ _).
  apply (concat (concat_p1 _)), ap. apply n.2.
Defined.

Definition nullhomot_paths_from_susp {X Z: Type} (H_N H_S : Z) (f : X -> H_N = H_S)
  (n : NullHomotopy (Susp_rec H_N H_S f))
: NullHomotopy f.
Proof.
  exists (n.2 North @ (n.2 South)^).
  intro x. apply moveL_pV.
  transitivity (ap (Susp_rec H_N H_S f) (merid x) @ n.2 South).
  - apply whiskerR, inverse, Susp_rec_beta_merid.
  - refine (concat_Ap n.2 (merid x) @ _).
    apply (concatR (concat_p1 _)), whiskerL. apply ap_const.
Defined.
