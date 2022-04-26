Require Import Types Basics WildCat Pointed Homotopy.ExactSequence HIT.epi.
Require Import AbGroups.AbelianGroup AbGroups.AbPushout.
Require Import AbSES.Core.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * Pushouts of short exact sequences *)

Definition abses_pushout0 `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : AbSES B A -> AbSES B A'.
Proof.
  intro E.
  snrapply (Build_AbSES (ab_pushout f (inclusion E))
                        ab_pushout_inl
                        (ab_pushout_rec grp_homo_const (projection E) _)).
  - symmetry; rapply iscomplex_abses.
  - rapply ab_pushout_embedding_inl.
  - nrapply (cancelR_issurjection ab_pushout_inr _).
    rapply (conn_map_homotopic _ (projection E)); symmetry.
    nrapply ab_pushout_rec_beta_right.
  - snrapply Build_IsExact.
    + srapply Build_pHomotopy.
      * nrapply ab_pushout_rec_beta_left.
      * apply path_ishprop.
    + intros [bc' p].
      rapply contr_inhabited_hprop.
      (** Pick a preimage under the quotient map. *)
      assert (bc : merely (hfiber grp_quotient_map bc')).
      1: apply issurj_class_of.
      strip_truncations.
      destruct bc as [[b c] q].
      (** The E-component of the preimage is in the kernel of [projection E]. *)
      assert (c_in_kernel : (projection E) c = mon_unit).
      1: { refine (_ @ p); symmetry.
           rewrite <- q; simpl.
           apply left_identity. }
      (** By exactness, we get an element in [A]. *)
      pose proof (a := isexact_preimage _ _ _ c c_in_kernel).
      strip_truncations.
      destruct a as [a s].
      (** Now we see that [bc'] lies in the image of [ab_pushout_inl]. *)
      assert (u : bc' = ab_pushout_inl (b + f a)).
      1: { rewrite <- q.
           apply path_ab_pushout; cbn.
           refine (tr (a; _)).
           apply path_prod; cbn.
           - apply grp_moveL_Mg.
             by rewrite negate_involutive.
           - exact (grp_homo_inv _ _ @ ap _ s @ (right_identity _)^). }
      apply tr.
      exists (b + f a); cbn.
      apply path_sigma_hprop; cbn.
      apply u^.
Defined.

(** ** The universal property of [abses_pushout_morphism] *)

Definition abses_pushout_morphism `{Univalence} {A A' B : AbGroup}
           (E : AbSES B A) (f : A $-> A')
  : AbSESMorphism E (abses_pushout0 f E).
Proof.
  snrapply (Build_AbSESMorphism f _ grp_homo_id).
  - exact ab_pushout_inr.
  - exact ab_pushout_commsq.
  - rapply ab_pushout_rec_beta_right.
Defined.

(** Any map [f : E -> F] of short exact sequences factors (uniquely) through [abses_pushout E f1]. *)

Definition abses_pushout_morphism_rec `{Univalence} {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : AbSESMorphism (abses_pushout0 (component1 f) E) F.
Proof.
  snrapply (Build_AbSESMorphism grp_homo_id _ (component3 f)).
  - rapply ab_pushout_rec.
    apply left_square.
  - intro x; simpl.
    rewrite grp_homo_unit.
    exact (right_identity _)^.
  - rapply (issurj_isepi_funext grp_quotient_map); intro x; simpl.
    refine (grp_homo_op (projection F) _ _ @ ap011 (+) _ _ @ (grp_homo_op _ _ _ )^).
    + refine (_ @ (grp_homo_unit _)^).
      apply iscomplex_abses.
    + apply right_square.
Defined.

(** The original map factors via the induced map. *)
Definition abses_pushout_morphism_rec_beta `{Univalence} (A B X Y : AbGroup)
           (E : AbSES B A) (F : AbSES Y X) (f : AbSESMorphism E F)
  : f = absesmorphism_compose (abses_pushout_morphism_rec f)
                              (abses_pushout_morphism E (component1 f)).
Proof.
  apply (equiv_ap issig_AbSESMorphism^-1 _ _).
  srapply path_sigma_hprop.
  1: apply path_prod.
  1: apply path_prod.
  all: apply equiv_path_grouphomomorphism; intro x; simpl.
  1,3: reflexivity.
  rewrite grp_homo_unit.
  exact (left_identity _)^.
Defined.
