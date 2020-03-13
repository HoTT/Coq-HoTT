(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Cat1.

(** * The unit category *)

CoFixpoint isglob_unit : IsGlob 0 Unit
  := Build_IsGlob 0 Unit (fun _ _ => Unit) (fun _ _ => isglob_unit).

Global Existing Instance isglob_unit.

CoFixpoint iscat0_unit : IsCat0 0 Unit.
Proof.
  snrapply Build_IsCat0.
  1,2,5: intros; exact tt.
  (** We cannot use isfunctor0_const since that requires IsCat0 *)
  1,2:
    intros ? ? ? ?; cofix e;
    simple notypeclasses refine (Build_IsFunctor0 _ _ _);
    intros ? ?; [ intro; exact tt | exact e ].
  intros a b.
  apply iscat0_unit.
Defined.

Global Existing Instance iscat0_unit.
