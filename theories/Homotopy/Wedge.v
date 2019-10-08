Require Import Basics.
Require Import Pointed.Core.
Require Import Colimits.Pushout.

(* Here we define the Wedge sum of two pointed types *)

Local Open Scope pointed_scope.

Definition Wedge (X Y : pType) : pType
  := Build_pType
    (Pushout (fun _ : Unit => point X) (fun _ => point Y))
    (pushl (point X)).

Notation "X \/ Y" := (Wedge X Y) : pointed_scope.

Definition wglue {X Y : pType}
  : pushl (point X) = (pushr (point Y) : X \/ Y) := pglue tt.

Definition wedge_incl {X Y : pType} : X \/ Y -> X * Y :=
 Pushout_rec _ (fun x => (x, point Y)) (fun y => (point X, y)) 
  (fun _ : Unit => idpath).
