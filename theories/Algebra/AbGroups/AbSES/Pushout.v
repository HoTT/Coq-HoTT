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
      (** Now the goal is to show that [bc'] lies in the image of [ab_pushout_inl]. *)
      apply tr.
      exists (b + - f (- a)); cbn.  (* It simplifies the algebra to write [- f(- a)] instead of [f a]. *)
      apply path_sigma_hprop; cbn.
      change (ab_pushout_inl (b + - f (- a)) = bc').  (* Just to guide the reader. *)
      refine (_ @ q).
      symmetry.
      apply path_ab_pushout; cbn.
      refine (tr (-a; _)).
      apply path_prod; cbn.
      * apply grp_moveL_Mg.
        by rewrite negate_involutive.
      * exact ((preserves_negate a) @ ap _ s @ (right_identity _)^).
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
  - snrapply (issurj_isepi_funext grp_quotient_map).
    1: apply issurj_class_of.
    2: exact _.
    intro x; simpl.
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

(** ** Functoriality of [abses_pushout0 f] *)

Global Instance is0functor_abses_pushout `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : Is0Functor (abses_pushout0 (B:=B) f).
Proof.
  srapply Build_Is0Functor;
    intros E F p.
  srapply abses_path_data_to_iso.
  srefine (functor_ab_pushout f f (inclusion _) (inclusion _) grp_homo_id grp_homo_id p.1 _ _; (_, _)).
  - reflexivity.
  - symmetry; exact (fst p.2).
  - nrapply ab_pushout_rec_beta_left.
  - srapply Quotient_ind_hprop.
    intro x; simpl.
    apply grp_cancelL.
    refine (snd p.2 (snd x) @ ap (projection F) _).
    exact (left_identity _)^.
Defined.

Definition abses_pushout_path_data_1 `{Univalence} {A A' B : AbGroup} (f : A $-> A') {E : AbSES B A} 
  : fmap (abses_pushout0 f) (Id E) = Id (abses_pushout0 f E).
Proof.
  srapply path_sigma_hprop.
  apply equiv_path_groupisomorphism.
  srapply Quotient_ind_hprop.
  intros [a' e]; simpl. (* This is true even on the representatives. *)
  apply qglue.
  refine (tr (0; _)).
  apply path_prod'; cbn.
  - refine (ap _ (grp_homo_unit _) @ _).
    refine (negate_mon_unit @ _).
    apply grp_moveL_Vg.
    exact (right_identity _ @ right_identity _).
  - refine (grp_homo_unit _ @ _).
    apply grp_moveL_Vg.
    exact (right_identity _ @ left_identity _).
Defined.

Definition ap_abses_pushout `{Univalence} {A A' B : AbGroup} (f : A $-> A')
           {E F : AbSES B A} (p : E = F)
  : ap (abses_pushout0 f) p
    = equiv_path_abses_iso (fmap (abses_pushout0 f) (equiv_path_abses_iso^-1 p)).
Proof.
  induction p.
  refine (_ @ ap _ _).
  2: refine ((abses_pushout_path_data_1 f)^ @ ap _ equiv_path_absesV_1^).
  exact equiv_path_abses_1^.
Defined.

Definition ap_abses_pushout_data `{Univalence} {A A' B : AbGroup} (f : A $-> A')
           {E F : AbSES B A} (p : E $== F)
  : ap (abses_pushout0 f) (equiv_path_abses_iso p)
    = equiv_path_abses_iso (fmap (abses_pushout0 f) p).
Proof.
  refine (ap_abses_pushout _ _ @ _).
  apply (ap (equiv_path_abses_iso o _)).
  apply eissect.
Defined.

Definition abses_pushout_point' `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : abses_pushout0 f (point (AbSES B A)) $== point _.
Proof.
  srapply abses_path_data_to_iso;
    srefine (_; (_,_)).
  - snrefine (ab_pushout_rec ab_biprod_inl _ _).
    + exact (functor_ab_biprod f grp_homo_id).
    + reflexivity.
  - intro a'. 
    apply path_prod.
    + simpl.
      exact (ap _ (grp_homo_unit f) @ right_identity _).
    + simpl.
      exact (right_identity _).
  - srapply Quotient_ind_hprop.
    reflexivity.
Defined.

Definition abses_pushout_point `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : abses_pushout0 f (point (AbSES B A)) = point _
  := equiv_path_abses_iso (abses_pushout_point' f).

Definition abses_pushout' `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : AbSES B A -->* AbSES B A'
  := Build_BasepointPreservingFunctor (abses_pushout0 f) (abses_pushout_point' f).

Definition abses_pushout `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : AbSES B A ->* AbSES B A'
  := to_pointed (abses_pushout' f).

Definition abses_pushout_compose' `{Univalence} {A0 A1 A2 B : AbGroup}
           (f : A0 $-> A1) (g : A1 $-> A2)
  : abses_pushout (B:=B) g o abses_pushout f $=> abses_pushout (g $o f).
Proof.
  intro E; apply gpd_rev.
  srapply abses_path_data_to_iso;
    srefine (_; (_,_)).
  - snrapply ab_pushout_rec.
    + apply inclusion.
    + exact (component2 (abses_pushout_morphism _ g)
                        $o component2 (abses_pushout_morphism _ f)).
    + intro a0.
      refine (left_square (abses_pushout_morphism _ g) _ @ _).
      exact (ap (component2 (abses_pushout_morphism (abses_pushout f E) g))
                (left_square (abses_pushout_morphism _ f) a0)).
  - apply ab_pushout_rec_beta_left.
  - srapply Quotient_ind_hprop.
    intro x; simpl.
    apply grp_cancelL; symmetry.
    exact (left_identity _ @ ap (projection E) (left_identity _)).
Defined.

Definition abses_pushout_compose `{Univalence} {A0 A1 A2 B : AbGroup}
           (f : A0 $-> A1) (g : A1 $-> A2)
  : abses_pushout (B:=B) g o abses_pushout f == abses_pushout (g $o f)
  := equiv_path_data_homotopy _ _ (abses_pushout_compose' f g).
