Require Import Basics Types.
Require Import Groups.Group.
Require Import Pointed.
Require Import WildCat.
Require Import Truncations.
Require Import Homotopy.Suspension.
Require Import Homotopy.ClassifyingSpace.
Require Import Homotopy.HomotopyGroup.

Local Open Scope pointed_scope.
Import ClassifyingSpaceNotation.

(** In this file we experiment with defining the free group on [A] to be the fundamental group of the suspension of [A + Unit]. *)

(** Note that this is NOT the definition of a free group that is used in the library. The definition in use will be exported in the file Algebra.Groups.FreeGroup. This file merely exists to serve as a demonstration that the free group *could* be defined this way.

This is not a very practical definition because we cannot even show that it is free at the time of writing, and univalence is used in a crucial way which seems overkill for a definition of freegroup. *)


(** TODO: Perhaps move this to the Pointed directory? *)
(** The free base point added to a type. This is in fact a functor and left adjoint to the forgetful functor pType to Type. *)
Definition pointify (S : Type) : pType := Build_pType (S + Unit) (inr tt).

(** pointify is left adjoint to forgetting the basepoint in the following sense *)
Theorem equiv_pointify_map `{Funext} (A : Type) (X : pType)
  : (pointify A ->* X) <~> (A -> X).
Proof.
  snrapply equiv_adjointify.
  1: exact (fun f => f o inl).
  { intros f.
    snrapply Build_pMap.
    { intros [a|].
      1: exact (f a).
      exact (point _). }
    reflexivity. }
  1: intro x; reflexivity.
  intros f.
  cbv.
  pointed_reduce.
  rapply equiv_path_pforall.
  snrapply Build_pHomotopy.
  1: by intros [a|[]].
  reflexivity.
Defined.

(** We can rephrase the universal property of the free group as a certain precomposition being an equivalence. *)
Definition isfreegroupon_isequiv_postcomp `{Funext} (F : Group) (A : Type) (i : A -> F)
  : (forall G, IsEquiv (fun f : F $-> G => f o i)) -> IsFreeGroupOn A F i.
Proof.
  intros k G g.
  specialize (k G).
  snrapply contr_equiv'.
  1: exact (hfiber (fun f x => grp_homo_map F G f (i x)) g).
  { rapply equiv_functor_sigma_id.
    intro y; symmetry.
    apply equiv_path_forall. }
  exact _.
Defined.

Section AssumeUnivalence.

  Context `{Univalence}.

  (** We define the free group as the 0-truncation of the loop space of the suspension of S + 1. Or in other words the fundamental group of the suspension of S + 1. *)
  Definition FreeGroup (S : Type) : Group
    := Pi1 (psusp (pointify S)).

  (** We can directly prove that it satisfies the desired equivalence. *)
  Theorem equiv_freegroup_rec (S : Type) (G : Group)
    : (FreeGroup S $-> G) <~> (S -> G).
  Proof.
    unfold FreeGroup.
    (** The first step is to swap the fundemantal group for the fundemantal group of a truncation. This will be important later. *)
    etransitivity.
    { srapply equiv_precompose_cat_equiv.
      1: exact (Pi1 (pTr 1 (psusp (pointify S)))).
      apply grp_iso_pi1_Tr. }
    (** Now we use the equivalence of group homomorphisms and pointed maps between their deloopings. *)
    etransitivity.
    1: rapply equiv_grp_homo_pmap_bg.
    (** Now since we have the classifying space of a fundamental group, we can change it into the original type. This lemma only works since the truncation is 1-truncated. *)
    etransitivity.
    { rapply equiv_pequiv_precompose.
      symmetry.
      nrapply pequiv_pclassifyingspace_pi1.
      1,3: exact _.
      apply isconnected_trunc.
      rapply isconnected_susp.
      rapply contr_inhabited_hprop.
      apply tr; exact (point _). }
    (** We can now get rid of the truncation by the universal property of trucation since BG is 1-truncated. *)
    etransitivity.
    1: rapply equiv_ptr_rec.
    (** Applying the loop-susp adjunction *)
    etransitivity.
    1: apply loop_susp_adjoint.
    (** Now we use the pointed equivalence between a group and the loop space of its delooping *)
    etransitivity.
    { rapply equiv_pequiv_postcompose.
      apply pequiv_loops_bg_g. }
    (** Finally we use the pointify adjunction. *)
    apply equiv_pointify_map.
  Defined.

  (** We can define the inclusion map by using the previous equivalence on the identity group homomorphism. *)
  Definition freegroup_incl (S : Type) : S -> FreeGroup S.
  Proof.
    rapply equiv_freegroup_rec.
    apply grp_homo_id.
  Defined.

  (** This in theory would allow us to prove that this definition of a free group is in fact a free group. We however run into trouble. We have to use [isequiv_homotopic'] since we are not using the specific map that the property of being a free group uses. However showing that these two maps are homotopic seems to be nontrivial. Coq struggles a lot working with the extreme amount of data needed to be unfolded here as well. Therefore we leave this instance as aborted. *)
  Global Instance isfreegroupon_freegroup (S : Type)
    : IsFreeGroupOn S (FreeGroup S) (freegroup_incl S).
  Proof.
    apply isfreegroupon_isequiv_postcomp.
    intro G.
    snrapply isequiv_homotopic'.
    1: apply equiv_freegroup_rec.
    intro f.
    unfold equiv_freegroup_rec.
    unfold transitive_equiv.
    unfold equiv_compose.
    unfold equiv_isequiv.
    (** It's not obvious how this can be finished. *)
  Abort.

End AssumeUnivalence.
