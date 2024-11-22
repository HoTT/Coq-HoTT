Require Import Basics Types Pointed WildCat.Core WildCat.Equiv.
Require Import Truncations.Core.
Require Import Homotopy.EMSpace.
Require Import Homotopy.HSpace.Core Homotopy.HSpace.Pointwise Homotopy.HSpace.HGroup Homotopy.HSpace.Coherent.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import Homotopy.Suspension.
Require Import Spheres HomotopyGroup.

Local Open Scope pointed_scope.

(** * Cohomology groups *)

(** Reduced cohomology groups are defined as the homotopy classes of pointed maps from the space to an Eilenberg-MacLane space. The group structure comes from the H-space structure on [K(G, n)]. *)
Definition Cohomology `{Univalence} (n : nat) (X : pType) (G : AbGroup) : AbGroup.
Proof.
  snrapply Build_AbGroup'.
  1: exact (Tr 0 (X ->** K(G, n))).
  1-3: shelve.
  nrapply isabgroup_ishabgroup_tr.
  nrapply ishabgroup_hspace_pmap. 
  apply iscohhabgroup_em.
Defined.

(** ** Cohomology of suspension *)

(** The (n+1)th cohomology of a suspension is the nth cohomology of the original space. *) 
(* TODO: show this preserves the operation somehow and is therefore a group iso *)
Definition cohomology_susp `{Univalence} n (X : pType) G
  : Cohomology n.+1 (psusp X) G <~> Cohomology n X G.
Proof.
  apply Trunc_functor_equiv.
  nrefine (_ oE (loop_susp_adjoint _ _)).
  rapply pequiv_pequiv_postcompose.
  symmetry.
  apply pequiv_loops_em_em.
Defined.

(** ** Cohomology of spheres *)

(* TODO: improve this to a group isomorphism once cohomology can be easily checked to be op preserving. *)
Definition cohomology_sn `{Univalence} (n : nat) (G : AbGroup)
  : Cohomology n.+1 (psphere n.+1) G <~> G.
Proof.
  nrefine (_ oE (equiv_tr 0 _)^-1).
  1: refine ?[goal1].
  2: { rapply istrunc_equiv_istrunc. symmetry. apply ?goal1. }
  nrefine (_ oE pmap_from_psphere_iterated_loops _ _).
  symmetry.
  rapply pequiv_loops_em_g.
Defined.
  