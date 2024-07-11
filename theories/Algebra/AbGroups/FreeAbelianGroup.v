Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import Types.Sigma Types.Forall Types.Paths.
Require Import WildCat.Core WildCat.EquivGpd.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.Abelianization.
Require Import Algebra.Groups.FreeGroup.

(** * Free Abelian Groups *)

Definition FactorsThroughFreeAbGroup (S : Type) (F_S : AbGroup)
  (i : S -> F_S) (A : AbGroup) (g : S -> A) : Type
  := {f : F_S $-> A & f o i == g}.

(** Universal property of a free abelian group on a set (type). *)
Class IsFreeAbGroupOn (S : Type) (F_S : AbGroup) (i : S -> F_S)
  := contr_isfreeabgroupon : forall (A : AbGroup) (g : S -> A),
      Contr (FactorsThroughFreeAbGroup S F_S i A g).
Global Existing Instance contr_isfreeabgroupon.

(** A abelian group is free if there exists a generating type on which it is a free group (a basis). *)
Class IsFreeAbGroup (F_S : AbGroup)
  := isfreegroup : {S : _ & {i : _ & IsFreeAbGroupOn S F_S i}}.

Global Instance isfreeabgroup_isfreeabgroupon (S : Type) (F_S : AbGroup) (i : S -> F_S)
  {H : IsFreeAbGroupOn S F_S i}
  : IsFreeAbGroup F_S
  := (S; i; H).

(** The abelianization of the free group on a set is the free abelian group. *)
Definition FreeAbGroup (S : Type) : AbGroup
  := abel (FreeGroup S).

(** The abelianization of a free group on a set is a free abelian group on that set. *)
Global Instance isfreeabgroupon_isabelianization_isfreegroup `{Funext}
  {S : Type} {G : Group} {A : AbGroup} (f : S -> G) (g : G $-> A)
  {H1 : IsAbelianization A g} {H2 : IsFreeGroupOn S G f}
  : IsFreeAbGroupOn S A (g o f).
Proof.
  unfold IsFreeAbGroupOn.
  intros B h.
  specialize (H2 B h).
  revert H2.
  unfold FactorsThroughFreeGroup, FactorsThroughFreeAbGroup.
  snrapply contr_equiv'.
  symmetry.
  exact (equiv_functor_sigma_pb (equiv_group_precomp_isabelianization g B)).
Defined.

(** As a special case, the free abelian group is a free abelian group. *)
Global Instance isfreeabgroup_freeabgroup `{Funext} (S : Type)
  : IsFreeAbGroup (FreeAbGroup S).
Proof.
  exists S.
  exists (abel_unit (FreeGroup S) o freegroup_in).
  srapply isfreeabgroupon_isabelianization_isfreegroup.
Defined.
