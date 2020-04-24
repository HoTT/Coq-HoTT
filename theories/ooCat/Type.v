(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1 ooCat.Paths ooCat.Forall.

(** * The oo-category of types *)

(** The universe is a globular type with functions, homotopies, and higher homotopies.  We obtain this by putting together path-groupoids with forall-categories. *)

(** The universe is a globular type *)
Global Instance isglob_type : IsGlob 1 Type
  := Build_IsGlob
       1 Type (fun A B => A -> B)
       (fun A B => isglob_forall (const B) (fun _ => isglob_withpaths B)).

(** The universe is a 0-coherent (oo,1)-category. *)
Global Instance iscat0_type : IsCat0 1 Type.
Proof.
  unshelve econstructor.
  - intros A B C g f; exact (g o f).
  - intros A; exact idmap.
  - intros A B C g; cbn.
    apply isfunctor0_postcompose.
    intros; apply isfunctor0_withpaths.
  - intros A B C f; cbn.
    rapply isfunctor0_precompose.
  - intros [].
  - intros A B.
    rapply iscat0_forall. 
    intros; rapply iscat0_withpaths.
Defined.

Global Existing Instances iscat0_type.
