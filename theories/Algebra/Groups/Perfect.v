Require Import Basics.Overture Basics.Tactics Basics.Equivalences Basics.Iff.
Require Import Types.Universe.
Require Import Groups.Group AbGroups.Abelianization AbGroups.AbelianGroup
  Groups.Commutator Groups.QuotientGroup.
Require Import WildCat.Core WildCat.Equiv.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope group_scope.

(** * Perfect Groups *)

(** ** Definition *)

(** A group is perfect if its abelianization is trivial. *)
Class IsPerfect (G : Group) := contr_abel_isperfect :: IsTrivialGroup (abel G).

(** A group is perfect if its commutator subgroup is the maximal subgroup. *)
Instance isperfect_maximal_commutator (G : Group)
  : IsMaximalSubgroup [G, G] -> IsPerfect G.
Proof.
  intros max.
  apply istrivial_iff_grp_iso_trivial.
  nrefine (_ $oE grp_iso_subgroup_group_maximal _).
  refine (_ $oE emap abgroup_group (@groupiso_isabelianization G _ _ _ _ _
    (isabelianization_derived_quotient _))).
  exact (fst (istrivial_iff_grp_iso_trivial (abgroup_derived_quotient G)) _
    $oE (grp_iso_subgroup_group_maximal _)^-1$).
Defined.

(** Conversely, the commutator subgroup of any perfect group is the maximal subgroup. *)
Definition ismaximalsubgroup_commutator_isperfect `{Univalence} (G : Group)
  : IsPerfect G -> IsMaximalSubgroup [G, G].
Proof.
  intros p.
  napply (ismaximalsubgroup_istrivial_grp_quotient _ (normalsubgroup_derived _)).
  srapply (istrivial_grp_iso (abel G)).
  nrefine (_^-1$ $oE _ $oE _).
  1,3: apply grp_iso_subgroup_group_maximal.
  exact (emap abgroup_group (@groupiso_isabelianization G _ _ _ _ _
    (isabelianization_derived_quotient _))).
Defined.

(** ** Basic properties *)
  
(** All simple non-abelian groups are perfect. *)
Definition isperfect_simple_nonabelian `{Univalence}
  (G : Group) {s : IsSimpleGroup G}
  (na : ~ Commutative (A:=G) (.*.))
  : IsPerfect G.
Proof.
  (** Since [G] is simple, we can assume the commutator [ [G, G] ] is either trivial or maximal. *)
  destruct (s [G, G] _) as [triv | max].
  2: by apply isperfect_maximal_commutator.
  contradiction na.
  intros x y.
  lhs napply grp_commutator_swap_op.
  lhs_V napply grp_assoc.
  rhs_V napply grp_unit_l.
  apply (ap (.* _)).
  apply triv.
  by apply subgroup_commutator_in.
Defined.

(** A quotient of a perfect group is perfect. *)
Definition isperfect_grp_quotient `{Univalence}
  (G : Group) (N : NormalSubgroup G)
  : IsPerfect G -> IsPerfect (G / N).
Proof.
  intros perf.
  apply isperfect_maximal_commutator.
  rapply grp_quotient_ind_hprop.
  intros x.
  apply ismaximalsubgroup_commutator_isperfect in perf.
  generalize (perf x); revert x.
  change ([G / N, G / N] (grp_quotient_map ?x))
    with (subgroup_preimage grp_quotient_map [G / N, G / N] x).
  napply subgroup_commutator_rec.
  intros x y _ _.
  change ([G / N, G / N] (grp_quotient_map (grp_commutator x y))).
  rewrite grp_homo_commutator.
  by apply subgroup_commutator_in.
Defined.
