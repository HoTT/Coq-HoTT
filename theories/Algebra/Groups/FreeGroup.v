Require Import Basics Types.
Require Import Groups.Group.
Require Import WildCat.

(** Free groups are defined in Group.v. In this file we prove properties of free groups. There are various constructions of free groups to choose from, all of which can be found in the FreeGroup folder. *)

(** In this file, and in the rest of the library we choose a modified version of the free group which can be found in Kraus-Altenkirch 2018 arXiv:1805.02069. This is a very simple HIT in a similar manner to the abelianization HIT used in Algebra.AbGroup.Abelianization. *)
Require Export Algebra.Groups.FreeGroup.KrausAltenkirch.

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

(** The above theorem is true regardless of the implementation of free groups. This let's us state the more specific theorem about the free groups themselves. This can be read as [FreeGroup] is left adjoint to the forgetful functor [group_type]. *)
Theorem equiv_freegroup_rec `{Funext} (G : Group) (A : Type)
  : (FreeGroup A $-> G) <~> (A -> G).
Proof.
  rapply equiv_isfreegroup_rec.
Defined.

(** TODO: Nielsen-Schreier theorem: Subgroups of free groups are free. Proofs of this statement are non-trivial. We can prove it using covering spaces which haven't yet been considered in this library. In fact, every known proof requires the axiom of choice in some crucical way. *)

(** Here is a sketch of such a proof. If F is a free group on a type X, then it is the fundamental group of the suspension of (X + 1) (This coule be by definition). A subgroup is then the fundamental group of a covering space of Susp (X + 1). This space is a connected 1-type and using choice we can show it has a spanning tree (since it is a topological graph). By shrinking the spanning tree we get that this cover is also the suspension of some non-empty type, hence is a free group. This "proof" is however a sketch and there may be serious problems when allowing groups to be free over arbitrary types. *)

(** TODO: If F(A) $<~> F(B) then the cardinalities of [A] and [B] are the same. *)

(** A proof might go like this: If F(A) $<~> F(B) then so are their abelianizations F(A)^ab $<~> F(B)^ab. It can be shown that F(A)^ab = Z^A hence we need only compare ranks of free abelian groups. It is not clear to me at the time of writing that this is now easier to prove however. *)

