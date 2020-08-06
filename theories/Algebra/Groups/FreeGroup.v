Require Import Basics Types.
Require Import Groups.Group.
Require Import WildCat.

(** Free groups are defined in Group.v. In this file we prove properties of free groups. There are various constructions of free groups to choose from, all of which can be found in the FreeGroup folder. Though, this is a bit of a lie since currently there is only one full implmentation. O:-) *)

(** In this file, and in the rest of the library we choose a modified version of the free group which can be found in Kraus-Altenkirch 2018 arXiv:1805.02069. This is a very simple HIT in a similar manner to the abelianization HIT used in Algebra.AbGroup.Abelianization. *)
Require Export Algebra.Groups.FreeGroup.ListQuotient.

(** Properties of free groups *)

(** We can state the universal property of free groups as an equivalence: (F(A) $-> G) <~> (A -> G) *)
Theorem equiv_isfreegroup_rec `{Funext} (G F : Group) (A : Type) (i : A -> F)
  `{IsFreeGroupOn A F i}
  : (F $-> G) <~> (A -> G).
Proof.
  snrapply Build_Equiv.
  { intros f.
    exact (f o i). }
  nrapply isequiv_contr_map.
  intro f.
  unfold hfiber.
  snrapply contr_equiv'.
  1: exact (FactorsThroughFreeGroup A F i G f).
  { rapply equiv_functor_sigma_id.
    intro g.
    apply equiv_path_forall. }
  exact _.
Defined.

(** The above theorem is true regardless of the implementation of free groups. This lets us state the more specific theorem about the canonical free groups. This can be read as [FreeGroup] is left adjoint to the forgetful functor [group_type]. *)
Theorem equiv_freegroup_rec `{Funext} (G : Group) (A : Type)
  : (FreeGroup A $-> G) <~> (A -> G).
Proof.
  rapply equiv_isfreegroup_rec.
Defined.

Global Instance ishprop_isfreegroupon `{Funext} (F : Group) (A : Type) (i : A -> F)
  : IsHProp (IsFreeGroupOn A F i).
Proof.
  unfold IsFreeGroupOn.
  apply trunc_forall.
Defined.

(** Both ways of stating the universal property are equivalent. *)
Definition equiv_isfregroupon_isequiv_precomp `{Funext} (F : Group) (A : Type) (i : A -> F)
  : IsFreeGroupOn A F i <~> forall G, IsEquiv (fun f : F $-> G => f o i).
Proof.
  srapply equiv_iff_hprop.
  1: intros k G; rapply (equiv_isequiv (equiv_isfreegroup_rec G F A i)).
  intros k G g.
  specialize (k G).
  snrapply contr_equiv'.
  1: exact (hfiber (fun f x => grp_homo_map F G f (i x)) g).
  { rapply equiv_functor_sigma_id.
    intro y; symmetry.
    apply equiv_path_forall. }
  exact _.
Defined.
