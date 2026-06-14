From HoTT Require Import Basics Types Truncations.Core.
From HoTT.WildCat Require Import Core.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import Algebra.Rings.Ring Algebra.Rings.Module Algebra.Rings.Vector.

Local Open Scope mc_add_scope.

(** * Finitely generated and finitely presented modules

    Following Christensen and Flaten, Definition 2.6.1. *)

(** The free module [R^n]. *)
Definition module_rn (R : Ring) (n : nat) : LeftModule R
  := Build_LeftModule R (abgroup_vector R n) (isleftmodule_isleftmodule_vector R n).

(** A module is finitely generated if some [R^n] surjects onto it. *)
Definition IsFinitelyGenerated {R : Ring} (M : LeftModule R) : Type
  := merely { n : nat
       & { f : LeftModuleHomomorphism (module_rn R n) M & IsSurjection f } }.

(** A module is finitely presented if it admits a finite presentation: an
    [R^n] surjecting onto it whose kernel is the image of some [R^m]. *)
Definition IsFinitelyPresented {R : Ring} (M : LeftModule R) : Type
  := merely { n : nat
       & { f : LeftModuleHomomorphism (module_rn R n) M
         & IsSurjection f
           * merely { m : nat
               & { g : LeftModuleHomomorphism (module_rn R m) (module_rn R n)
                 & forall x, (f x = 0) <-> hexists (fun y => g y = x) } } } }.
