Require Import AbelianGroup.
Require Import HoTT.Basics HoTT.Types.
Require Import Truncations HSet.
Require Import Colimits.Coeq.
Require Export Algebra.Groups.
Require Import Cubical.
Require Import WildCat.
Require Import Biproduct.

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
Global Instance negate_hom (A : Group) (B : AbGroup)
  : Negate (@Hom Group _ A B) := grp_homo_compose ab_homo_negation.

(** For [A, B : AbGroup], homomorphisms A $-> B form an abelian group.  *)
Definition grp_hom `{Funext} (A : Group) (B : AbGroup) : Group.
Proof.
  nrefine (Build_Group
              (GroupHomomorphism A B)
              (fun f g => grp_homo_compose ab_codiagonal (grp_prod_corec f g))
              grp_homo_const
              (@negate_hom _ _) _).
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
