Require Import WildCat HSet Truncations.
Require Import AbelianGroup Biproduct.

(** * Homomorphisms of abelian groups form an abelian group. *)

(** We can add group homomorphisms. *)
Definition ab_homo_add {A : Group} {B : AbGroup} (f g : A $-> B)
  : A $-> B.
Proof.
  refine (grp_homo_compose ab_codiagonal _).
  (** [fun a => f(a) + g(a)] **)
  exact (grp_prod_corec f g).
Defined.

(** We can negate an abelian group homomorphism by composing with ab_homo_negation. *)
Global Instance negate_hom {A : Group} {B : AbGroup}
  : Negate (@Hom Group _ A B) := grp_homo_compose ab_homo_negation.

(** For [A B : AbGroup], homomorphisms [A $-> B] form an abelian group. *)
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

Global Instance isbifunctor_ab_hom `{Funext}
  : IsBifunctor (ab_hom : Group^op -> AbGroup -> AbGroup).
Proof.
  snrapply Build_IsBifunctor.
  1-2: exact _.
  intros A A' f B B' g phi; cbn.
  by apply equiv_path_grouphomomorphism.
Defined.

(** ** Properties of [ab_hom] *)

(** Precomposition with a surjection is an embedding. *)
(* This could be deduced from [isembedding_precompose_surjection_hset], but relating precomposition of homomorphisms with precomposition of the underlying maps is tedious, so we give a direct proof. *)
Global Instance isembedding_precompose_surjection_ab `{Funext} {X Y Z : AbGroup}
  (f : X $-> Y) `{IsSurjection f}
  : IsEmbedding (fmap10 (A:=Group^op) ab_hom f Z).
Proof.
  apply isembedding_isinj_hset; intros g0 g1 p.
  apply equiv_path_grouphomomorphism.
  rapply (conn_map_elim (Tr (-1)) f).
  exact (equiv_path_grouphomomorphism^-1 p).
Defined.
