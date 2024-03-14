Require Import Basics Types.
Require Import WildCat HSet Truncations.Core Modalities.ReflectiveSubuniverse.
Require Import AbelianGroup Biproduct.

(** * Homomorphisms from a group to an abelian group form an abelian group. *)

(** We can add group homomorphisms. *)
Definition ab_homo_add {A : Group} {B : AbGroup} (f g : A $-> B)
  : A $-> B.
Proof.
  refine (grp_homo_compose ab_codiagonal _).
  (** [fun a => f(a) + g(a)] **)
  exact (grp_prod_corec f g).
Defined.

(** We can negate a group homomorphism by composing with [ab_homo_negation]. *)
Global Instance negate_hom {A : Group} {B : AbGroup}
  : Negate (@Hom Group _ A B) := grp_homo_compose ab_homo_negation.

(** For [A] and [B] groups, with [B] abelian, homomorphisms [A $-> B] form an abelian group. *)
Definition grp_hom `{Funext} (A : Group) (B : AbGroup) : Group.
Proof.
  nrefine (Build_Group (GroupHomomorphism A B)
             ab_homo_add grp_homo_const negate_hom _).
  repeat split.
  1: exact _.
  all: hnf; intros; apply equiv_path_grouphomomorphism; intro; cbn.
  + apply associativity.
  + apply left_identity.
  + apply right_identity.
  + apply left_inverse.
  + apply right_inverse.
Defined.

Definition ab_hom `{Funext} (A : Group) (B : AbGroup) : AbGroup.
Proof.
  snrapply (Build_AbGroup (grp_hom A B)).
  intros f g; cbn.
  apply equiv_path_grouphomomorphism; intro x; cbn.
  apply commutativity.
Defined.

(** ** The bifunctor [ab_hom] *)

Global Instance is0functor_ab_hom01 `{Funext} {A : Group^op}
  : Is0Functor (ab_hom A).
Proof.
  snrapply (Build_Is0Functor _ AbGroup); intros B B' f.
  snrapply Build_GroupHomomorphism.
  1: exact (fun g => grp_homo_compose f g).
  intros phi psi.
  apply equiv_path_grouphomomorphism; intro a; cbn.
  exact (grp_homo_op f _ _).
Defined.

Global Instance is0functor_ab_hom10 `{Funext} {B : AbGroup@{u}}
  : Is0Functor (flip (ab_hom : Group^op -> AbGroup -> AbGroup) B).
Proof.
  snrapply (Build_Is0Functor (Group^op) AbGroup); intros A A' f.
  snrapply Build_GroupHomomorphism.
  1: exact (fun g => grp_homo_compose g f).
  intros phi psi.
  by apply equiv_path_grouphomomorphism.
Defined.

Global Instance is1functor_ab_hom01 `{Funext} {A : Group^op}
  : Is1Functor (ab_hom A).
Proof.
  nrapply Build_Is1Functor.
  - intros B B' f g p phi.
    apply equiv_path_grouphomomorphism; intro a; cbn.
    exact (p (phi a)).
  - intros B phi.
    by apply equiv_path_grouphomomorphism.
  - intros B C D f g phi.
    by apply equiv_path_grouphomomorphism.
Defined.

Global Instance is1functor_ab_hom10 `{Funext} {B : AbGroup@{u}}
  : Is1Functor (flip (ab_hom : Group^op -> AbGroup -> AbGroup) B).
Proof.
  nrapply Build_Is1Functor.
  - intros A A' f g p phi.
    apply equiv_path_grouphomomorphism; intro a; cbn.
    exact (ap phi (p a)).
  - intros A phi.
    by apply equiv_path_grouphomomorphism.
  - intros A C D f g phi.
    by apply equiv_path_grouphomomorphism.
Defined.

Global Instance is0bifunctor_ab_hom `{Funext}
  : Is0Bifunctor (ab_hom : Group^op -> AbGroup -> AbGroup).
Proof.
  rapply Build_Is0Bifunctor.
Defined.

Global Instance is1bifunctor_ab_hom `{Funext}
  : Is1Bifunctor (ab_hom : Group^op -> AbGroup -> AbGroup).
Proof.
  rapply Build_Is1Bifunctor.
  intros A A' f B B' g phi; cbn.
  by apply equiv_path_grouphomomorphism.
Defined.

(** ** Properties of [ab_hom] *)

(** Precomposition with a surjection is an embedding. *)
(* This could be deduced from [isembedding_precompose_surjection_hset], but relating precomposition of homomorphisms with precomposition of the underlying maps is tedious, so we give a direct proof. *)
Global Instance isembedding_precompose_surjection_ab `{Funext} {A B C : AbGroup}
  (f : A $-> B) `{IsSurjection f}
  : IsEmbedding (fmap10 (A:=Group^op) ab_hom f C).
Proof.
  apply isembedding_isinj_hset; intros g0 g1 p.
  apply equiv_path_grouphomomorphism.
  rapply (conn_map_elim (Tr (-1)) f).
  exact (equiv_path_grouphomomorphism^-1 p).
Defined.
