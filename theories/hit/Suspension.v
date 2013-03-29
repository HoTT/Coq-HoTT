(* -*- mode: coq; mode: visual-line -*- *)

(** * The suspension of a type *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* ** Definition of suspension. *)

Module Export Suspension.

Local Inductive Susp (X : Type) : Type :=
  | North : Susp X
  | South : Susp X.

Global Arguments North {X}.
Global Arguments South {X}.

Axiom merid : forall (X : Type) (x : X), North = South :> Susp X.
Global Arguments merid {X} x.

Definition Susp_rect {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
: forall (y:Susp X), P y
:= fun y => match y with North => H_N | South => H_S end.

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
  path_via (apD (Susp_rect_nd H_N H_S H_merid) (merid x)).
  symmetry; refine (apD_const (Susp_rect_nd H_N H_S H_merid) _).
  refine (Susp_comp_merid (fun _ : Susp X => Y) _ _ _ _).
Defined.