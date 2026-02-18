From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core Opposite Bifunctor AbEnriched.
Require Import HSet Truncations.Core Modalities.ReflectiveSubuniverse.
Require Import Groups.Group AbelianGroup Biproduct.

(** * Homomorphisms from a group to an abelian group form an abelian group. *)

(** In this file, we use additive notation for the group operation, even though some of the groups we deal with are not assumed to be abelian. *)
Local Open Scope mc_add_scope.

(** The sum of group homomorphisms [f] and [g] is [fun a => f(a) + g(a)].  While the group *laws* require [Funext], the operations do not, so we make them instances. *)
Instance sgop_hom {A : Group} {B : AbGroup} : SgOp (A $-> B).
Proof.
  intros f g.
  exact (grp_homo_compose ab_codiagonal (grp_prod_corec f g)).
Defined.

(** We can negate a group homomorphism [A -> B] by post-composing with [ab_homo_negation : B -> B]. *)
Instance inverse_hom {A : Group} {B : AbGroup}
  : Inverse (@Hom Group _ A B) := grp_homo_compose ab_homo_negation.

(** For [A] and [B] groups, with [B] abelian, homomorphisms [A $-> B] form an abelian group. *)
Definition grp_hom `{Funext} (A : Group) (B : AbGroup) : Group.
Proof.
  snapply (Build_Group' (GroupHomomorphism A B) sgop_hom grp_homo_const inverse_hom).
  1: exact _.
  all: hnf; intros; apply equiv_path_grouphomomorphism; intro; cbn.
  - apply associativity.
  - apply left_identity.
  - apply left_inverse.
Defined.

Definition ab_hom `{Funext} (A : Group) (B : AbGroup) : AbGroup.
Proof.
  snapply (Build_AbGroup (grp_hom A B)).
  intros f g; cbn.
  apply equiv_path_grouphomomorphism; intro x; cbn.
  apply commutativity.
Defined.

(** ** The bifunctor [ab_hom] *)

Instance is0functor_ab_hom01 `{Funext} {A : Group^op}
  : Is0Functor (ab_hom A).
Proof.
  snapply Build_Is0Functor; intros B B' f.
  snapply Build_GroupHomomorphism.
  1: exact (fun g => grp_homo_compose f g).
  intros phi psi.
  apply equiv_path_grouphomomorphism; intro a; cbn.
  exact (grp_homo_op f _ _).
Defined.

Instance is0functor_ab_hom10 `{Funext} {B : AbGroup@{u}}
  : Is0Functor (flip (ab_hom : Group^op -> AbGroup -> AbGroup) B).
Proof.
  snapply Build_Is0Functor; intros A A' f.
  snapply Build_GroupHomomorphism.
  1: exact (fun g => grp_homo_compose g f).
  intros phi psi.
  by apply equiv_path_grouphomomorphism.
Defined.

Instance is1functor_ab_hom01 `{Funext} {A : Group^op}
  : Is1Functor (ab_hom A).
Proof.
  napply Build_Is1Functor.
  - intros B B' f g p phi.
    apply equiv_path_grouphomomorphism; intro a; cbn.
    exact (p (phi a)).
  - intros B phi.
    by apply equiv_path_grouphomomorphism.
  - intros B C D f g phi.
    by apply equiv_path_grouphomomorphism.
Defined.

Instance is1functor_ab_hom10 `{Funext} {B : AbGroup@{u}}
  : Is1Functor (flip (ab_hom : Group^op -> AbGroup -> AbGroup) B).
Proof.
  napply Build_Is1Functor.
  - intros A A' f g p phi.
    apply equiv_path_grouphomomorphism; intro a; cbn.
    exact (ap phi (p a)).
  - intros A phi.
    by apply equiv_path_grouphomomorphism.
  - intros A C D f g phi.
    by apply equiv_path_grouphomomorphism.
Defined.

Instance is0bifunctor_ab_hom `{Funext}
  : Is0Bifunctor (ab_hom : Group^op -> AbGroup -> AbGroup)
  := Build_Is0Bifunctor'' _.

Instance is1bifunctor_ab_hom `{Funext}
  : Is1Bifunctor (ab_hom : Group^op -> AbGroup -> AbGroup).
Proof.
  napply Build_Is1Bifunctor''.
  1,2: exact _.
  intros A A' f B B' g phi; cbn.
  by apply equiv_path_grouphomomorphism.
Defined.

(** ** [AbGroup] has a wild enrichment in wild abelian groups *)

(** Using arguments very similar to the above, but without using [Funext], we can show that [AbGroup] is enriched in the wild sense.  We could use this combined with [Funext] to deduce the results above, but we wouldn't get the extra generality where the domain group does not need to be abelian.  And conversely we don't want to use the above results here, since we don't need to rely on [Funext]. *)

Instance abenriched_abgroup : IsAbEnriched AbGroup.
Proof.
  snapply Build_IsAbEnriched.
  - intros A B.
    snapply (Build_IsAbGroup_0gpd _ _ _ _ sgop_hom grp_homo_const inverse_hom).
    3-8: hnf; intros; intro; cbn.
    + srapply Build_Is0Bifunctor'.
      snapply Build_Is0Functor.
      intros [f f'] [g g'] [p p'] a; cbn in *.
      exact (ap011 _ (p a) (p' a)).
    + snapply Build_Is0Functor.
      intros f g p a; cbn.
      apply (ap _ (p a)).
    + symmetry; apply associativity.
    + apply left_identity.
    + apply right_identity.
    + apply left_inverse.
    + apply right_inverse.
    + apply commutativity.
  - intros A B C g f f' a; cbn.
    apply grp_homo_op.
  - intros A B C f g g' a; cbn. reflexivity.
Defined.

(** ** Properties of [ab_hom] *)

(** Precomposition with a surjection is an embedding. *)
(* This could be deduced from [isembedding_precompose_surjection_hset], but relating precomposition of homomorphisms with precomposition of the underlying maps is tedious, so we give a direct proof. *)
Instance isembedding_precompose_surjection_ab `{Funext} {A B C : AbGroup}
  (f : A $-> B) `{IsSurjection f}
  : IsEmbedding (fmap10 (A:=Group^op) ab_hom f C).
Proof.
  apply isembedding_isinj_hset; intros g0 g1 p.
  apply equiv_path_grouphomomorphism.
  rapply (conn_map_elim (Tr (-1)) f).
  exact (equiv_path_grouphomomorphism^-1 p).
Defined.
