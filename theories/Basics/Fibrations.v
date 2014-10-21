(** * Basic facts about fibrations *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(* *** Homotopy fibers *)

(** Homotopy fibers are homotopical inverse images of points.  *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

(** *** Replacing a map with a fibration *)

Definition equiv_fibration_replacement  {B C} (f:C ->B):
  C <~> {y:B & hfiber f y}.
Proof.
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               C {y:B & {x:C & f x = y}}
               (fun c => (f c; (c; idpath)))
               (fun c => c.2.1)
               _
               (fun c => idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
Defined.

Definition hfiber_fibration {X} (x : X) (P:X->Type):
    P x <~> @hfiber (sigT P) X pr1 x.
Proof.
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               (P x) { z : sigT P & z.1 = x }
               (fun Px => ((x; Px); idpath))
               (fun Px => transport P Px.2 Px.1.2)
               _
               (fun Px => idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
Defined.
