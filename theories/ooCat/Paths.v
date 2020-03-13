(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1.

Generalizable Variables A B.

(** * Path oo-groupoids *)

(** Every type is a globular type with its tower of identity types. *)
CoFixpoint isglob_withpaths (A : Type) : IsGlob 0 A.
Proof.
  exists (@paths A); intros.
  apply isglob_withpaths.
Defined.

(** We could make this a global but low-priority instance, but doing so seems to break stuff later. *)
(* Global Existing Instance isglob_withpaths | 1000. *)
Local Existing Instance isglob_withpaths.

(** Any function is a 0-coherent oo-functor between types equipped with their globular tower of identity types.  As for [isglob_withpaths], we don't make this an [Instance]. *)
CoFixpoint isfunctor0_withpaths {A B : Type} (F : A -> B)
  : IsFunctor0 F.
Proof.
  refine (Build_IsFunctor0 F _ _).
  exact (@ap A B F).
  (** The coinductive assumption is found by typeclass search. *)
Defined.

Local Existing Instance isfunctor0_withpaths.

(** The tower of identity types is a 0-coherent oo-category with path composition.  Again, not an [Instance]. *)
CoFixpoint iscat0_withpaths (A : Type) : IsCat0 0 A.
Proof.
  unshelve econstructor.
  - intros a b c p q; exact (q @ p).
  - intros a; exact idpath.
  - intros; cbn; apply isfunctor0_withpaths.
  - intros; cbn; apply isfunctor0_withpaths.
  - intros ? a b f; exact (f^).
  - intros; apply iscat0_withpaths.
Defined.

Local Existing Instance iscat0_withpaths.

(** TODO: Any dependent type should be a displayed 0-coherent oo-category with its tower of dependent identity types. *)

(** Every path is a quasi-isomorphism. *)
CoFixpoint isqiso_withpaths {A : Type} {a b : A} (p : a = b)
  : IsQIso p.
Proof.
  unshelve econstructor.
  - exact (p^).
  - cbn. apply concat_pV.
  - cbn. apply concat_Vp.
  - apply isqiso_withpaths.
  - apply isqiso_withpaths.
Defined.

(** TODO: 1-coherent functors, 1-coherent categories *)
