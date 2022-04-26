Require Import HoTT.Basics HoTT.Types HSet WildCat.
Require Import Groups AbGroups.AbelianGroup AbGroups.AbPullback AbGroups.AbPushout.
Require Import Homotopy.ExactSequence Pointed HFiber Limits.Pullback HIT.epi.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * Short exact sequences of abelian groups *)

(** A short exact sequence of abelian groups consists of a monomorphism [i : A -> E] and an epimorphism [p : E -> B] such that the image of [i] equals the kernel of [p]. Later we will consider short exact sequences up to isomorphism by 0-truncating the type [AbSES] defined below. An isomorphism class of short exact sequences is called an extension. *)

(** The type of short exact sequences [A -> E -> B] of abelian groups. We decorate it with (') to reserve the undecorated name for the structured version. *)
Record AbSES' {B A : AbGroup} := {
    middle :  AbGroup;
    inclusion : A $-> middle;
    projection : middle $-> B;
    isembedding_inclusion : IsEmbedding inclusion;
    issurjection_projection : IsSurjection projection;
    isexact_inclusion_projection : IsExact (Tr (-1)) inclusion projection;
  }.

(** Given a short exact sequence [A -> E -> B : AbSES B A], we coerce it to [E]. *)
Coercion middle : AbSES' >-> AbGroup.

Global Existing Instances isembedding_inclusion issurjection_projection isexact_inclusion_projection.

Arguments AbSES' B A : clear implicits.
Arguments Build_AbSES' {B A}.

Definition Build_AbSES {B A : AbGroup} := @Build_AbSES' B A.

(** TODO Figure out why printing this term eats memory and seems to never finish. *)
Local Definition issig_abses_do_not_print {B A : AbGroup} : _ <~> AbSES' B A := ltac:(issig).

(** [make_equiv] is slow if used in the context of the next result, so we give the abstract form of the goal here. *)
Local Definition issig_abses_helper {AG : Type} {P : AG -> Type} {Q : AG -> Type}
      {R : forall E, P E -> Type} {S : forall E, Q E -> Type} {T : forall E, P E -> Q E -> Type}
  : {X : {E : AG & P E * Q E} & R _ (fst X.2) * S _ (snd X.2) * T _ (fst X.2) (snd X.2)}
      <~> {E : AG & {H0 : P E & {H1 : Q E & {_ : R _ H0 & {_ : S _ H1 & T _ H0 H1}}}}}
  := ltac:(make_equiv).

(** A more useful organization of [AbSES'] as a sigma-type. *)
Definition issig_abses {B A : AbGroup}
  : {X : {E : AbGroup & (A $-> E) * (E $-> B)} &
           (IsEmbedding (fst X.2)
            * IsSurjection (snd X.2)
            * IsExact (Tr (-1)) (fst X.2) (snd X.2))}
      <~> AbSES' B A
  := issig_abses_do_not_print oE issig_abses_helper.

Definition iscomplex_abses {A B : AbGroup} (E : AbSES' B A)
  : IsComplex (inclusion E) (projection E)
  := cx_isexact.

(** [AbSES' B A] is pointed by the split sequence [A -> A+B -> B]. *)
Global Instance ispointed_abses {B A : AbGroup} : IsPointed (AbSES' B A).
Proof.
  rapply (Build_AbSES (ab_biprod A B) ab_biprod_inl ab_biprod_pr2).
  snrapply Build_IsExact.
  - srapply Build_pHomotopy.
    + reflexivity.
    + apply path_ishprop.
  - intros [[a b] p]; cbn; cbn in p.
    rapply contr_inhabited_hprop.
    apply tr.
    exists a.
    rapply path_sigma_hprop; cbn.
    exact (path_prod' idpath p^).
Defined.

(** The pointed type of short exact sequences. *)
Definition AbSES (B A : AbGroup) : pType := Build_pType (AbSES' B A) _.

(** Paths in [AbSES] correspond to isomorphisms between the [middle]s respecting [inclusion] and [projection]. Below we prove the stronger statement [equiv_path_abses], which uses this result. *)
Proposition equiv_path_abses_iso `{Univalence} {B A : AbGroup} (E F : AbSES B A)
  : {phi : GroupIsomorphism E F &
             (phi $o inclusion _ == inclusion _)
             * (projection _ $o grp_iso_inverse phi == projection _)}
      <~> E = F.
Proof.
  refine (equiv_ap_inv issig_abses _ _ oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  refine (equiv_path_sigma _ _ _ oE _).
  srapply equiv_functor_sigma'.
  1: exact equiv_path_abgroup.
  intro q; lazy beta.
  snrefine (equiv_concat_l _ _ oE _).
  1: exact (q $o inclusion _, projection _ $o grp_iso_inverse q).
  2: { refine (equiv_path_prod _ _ oE _).
       exact (equiv_functor_prod'
                equiv_path_grouphomomorphism
                equiv_path_grouphomomorphism). }
  refine (transport_prod _ _ @ _).
  apply path_prod'.
  - apply transport_iso_abgrouphomomorphism_from_const.
  - apply transport_iso_abgrouphomomorphism_to_const.
Defined.

(** ** Morphisms of short exact sequences *)

(** A morphism between short exact sequences is a natural transformation between the underlying diagrams. *)
Record AbSESMorphism {A X B Y : AbGroup} {E : AbSES B A} {F : AbSES Y X} := {
    component1 : A $-> X;
    component2 : middle E $-> middle F;
    component3 : B $-> Y;
    left_square : (inclusion _) $o component1 == component2 $o (inclusion _);
    right_square : (projection _) $o component2 == component3 $o (projection _);
  }.

Arguments AbSESMorphism {A X B Y} E F.
Arguments Build_AbSESMorphism {_ _ _ _ _ _} _ _ _ _ _.

Definition issig_AbSESMorphism {A X B Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X}
  : { f : (A $-> X) * (middle E $-> middle F) * (B $-> Y)
          & ((inclusion _) $o (fst (fst f)) == (snd (fst f)) $o (inclusion _))
            * ((projection F) $o (snd (fst f)) == (snd f) $o (projection _)) }
      <~> AbSESMorphism E F := ltac:(make_equiv).

Definition absesmorphism_compose {A0 A1 A2 B0 B1 B2 : AbGroup}
           {E : AbSES B0 A0} {F : AbSES B1 A1} {G : AbSES B2 A2}
           (g : AbSESMorphism F G) (f : AbSESMorphism E F)
  : AbSESMorphism E G.
Proof.
  rapply (Build_AbSESMorphism (component1 g $o component1 f)
                              (component2 g $o component2 f)
                              (component3 g $o component3 f)).
  - intro x; cbn.
    exact (left_square g _ @ ap _ (left_square f _)).
  - intro x; cbn.
    exact (right_square g _ @ ap _ (right_square f _)).
Defined.

(** ** Characterization of split short exact sequences *)

(* We characterize trivial short exact sequences in [AbSES] as those for which [projection] splits. *)

(** If [projection E] splits, we get an induced map [fun e => e - s (projection E e)] from [E] to [ab_kernel (projection E)]. *)
Definition projection_split_to_kernel {B A : AbGroup} (E : AbSES B A)
           {s : GroupHomomorphism B E} (h : projection _ $o s == idmap)
  : GroupHomomorphism E (@ab_kernel E B (projection _)).
Proof.
  snrapply (grp_kernel_corec (G:=E) (A:=E)).
  - exact (ab_homo_add grp_homo_id (ab_homo_negation $o s $o (projection _))).
  - intro x; simpl.
    refine (grp_homo_op (projection _) x _ @ _).
    refine (ap (fun y => (projection _) x + y) _ @ right_inverse ((projection _) x)).
    refine (grp_homo_inv _ _ @ ap (-) _ ).
    apply h.
Defined.

(** The composite [A -> E -> ab_kernel (projection E)] is [grp_cxfib]. *)
Lemma projection_split_to_kernel_beta {B A : AbGroup} (E : AbSES B A)
      {s : GroupHomomorphism B E} (h : (projection _) $o s == idmap)
  : projection_split_to_kernel E h $o (inclusion _) == grp_cxfib cx_isexact.
Proof.
  intro a.
  apply path_sigma_hprop; cbn.
  apply grp_cancelL1.
  refine (ap (fun x => - s x) _ @ _).
  1: rapply cx_isexact.
  exact (ap _ (grp_homo_unit _) @ negate_mon_unit).
Defined.

(** The induced map [E -> ab_kernel (projection E) + B] is an isomorphism. We suffix it with 1 since it is the first composite in the desired isomorphism [E -> A + B]. *)
Definition projection_split_iso1 {B A : AbGroup} (E : AbSES B A)
           {s : GroupHomomorphism B E} (h : (projection _) $o s == idmap)
  : GroupIsomorphism E (ab_biprod (@ab_kernel E B (projection _)) B).
Proof.
  srapply Build_GroupIsomorphism.
  - refine (ab_biprod_corec _ (projection _)).
    exact (projection_split_to_kernel E h).
  - srapply isequiv_adjointify.
    + refine (ab_biprod_rec _ s).
      rapply subgroup_incl.
    + intros [a b]; simpl.
      apply path_prod'.
      * srapply path_sigma_hprop; cbn.
        refine ((associativity _ _ _)^ @ _).
        apply grp_cancelL1.
        refine (ap _ _ @ right_inverse _).
        apply (ap (-)).
        apply (ap s).
        refine (grp_homo_op (projection _) a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
      * refine (grp_homo_op (projection _) a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
    + intro e; simpl.
      by apply grp_moveR_gM.
Defined.

(** The full isomorphism [E -> A + B]. *)
Definition projection_split_iso {B A : AbGroup} (E : AbSES B A)
           {s : GroupHomomorphism B E} (h : (projection _) $o s == idmap)
  : GroupIsomorphism E (ab_biprod A B).
Proof.
  etransitivity (ab_biprod (ab_kernel _) B).
  - exact (projection_split_iso1 E h).
  - srapply (equiv_functor_ab_biprod (grp_iso_inverse _) grp_iso_id).
    rapply grp_iso_cxfib.
Defined.

Proposition projection_split_beta {B A : AbGroup} (E : AbSES B A)
            {s : GroupHomomorphism B E} (h : (projection _) $o s == idmap)
  : projection_split_iso E h $o (inclusion _) == ab_biprod_inl.
Proof.
  intro a.
  refine (ap _ (ab_corec_beta _ _ _ _) @ _).
  refine (ab_biprod_functor_beta _ _ _ _ _ @ _).
  nrapply path_prod'.
  2: rapply cx_isexact.
  refine (ap _ (projection_split_to_kernel_beta E h a) @ _).
  apply eissect.
Defined.

(** A short exact sequence [E] in [AbSES B A] is trivial if and only if [projection E] splits. *)
Proposition iff_abses_trivial_split `{Univalence} {B A : AbGroup} (E : AbSES B A)
  : {s : GroupHomomorphism B E & (projection _) $o s == idmap}
    <-> (E = point (AbSES B A)).
Proof.
  refine (iff_compose _ (iff_equiv (equiv_path_abses_iso _ _))); split.
  - intros [s h].
    exists (projection_split_iso E h).
    split.
    + apply projection_split_beta.
    + intros [a b]; simpl.
      refine (grp_homo_op (projection _)  _ _ @ _).
      refine (ap011 (+) _ (h _) @ _).
      1: rapply cx_isexact.
      apply left_identity.
  - intros [phi [g h]].
    exists (grp_homo_compose (grp_iso_inverse phi) ab_biprod_inr).
    intro x.
    exact (h (ab_biprod_inr x)).
Defined.

(** ** Pullbacks of short exact sequences *)

(** A short exact sequence [A -> E -> B] can be pulled back along a map [B' -> B]. *)
Lemma abses_pullback {A B B' : AbGroup} (E : AbSES B A) (f : B' $-> B) : AbSES B' A.
Proof.
  snrapply (Build_AbSES (ab_pullback (projection E) f)
                        (grp_pullback_corec _ _ (inclusion _) grp_homo_const _)
                        (grp_pullback_pr2 (projection _) f)).
  - intro x.
    nrefine (_ @ (grp_homo_unit f)^).
    apply isexact_inclusion_projection.
  - exact (cancelL_isembedding (g:= grp_pullback_pr1 _ _)).
  - rapply conn_map_pullback'.
  - snrapply Build_IsExact.
    + srapply Build_pHomotopy.
      * reflexivity.
      * apply path_ishprop.
    + nrefine (cancelR_equiv_conn_map
                 _ _ (hfiber_pullback_along_pointed f (projection _) (grp_homo_unit _))).
      nrefine (conn_map_homotopic _ _ _ _ (conn_map_isexact (IsExact:=isexact_inclusion_projection _))).
      intro a.
      by apply path_sigma_hprop.
Defined.

(** The natural map from the pulled back sequence. *)
Definition abses_pullback_morphism {A B B' : AbGroup} (E : AbSES B A) (f : B' $-> B)
  : AbSESMorphism (abses_pullback E f) E.
Proof.
  snrapply (Build_AbSESMorphism grp_homo_id _ f).
  - apply grp_pullback_pr1.
  - reflexivity.
  - apply pullback_commsq.
Defined.

(** *** The universal property of [abses_pullback_morphism] *)

(* Any map [f : E -> F] of short exact sequences factors (uniquely) through [abses_pullback F f3]. *)

Definition abses_pullback_morphism_corec {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : AbSESMorphism E (abses_pullback F (component3 f)).
Proof.
  snrapply (Build_AbSESMorphism (component1 f) _ grp_homo_id).
  - apply (grp_pullback_corec (projection F) (component3 f)
                              (component2 f) (projection E)).
    apply right_square.
  - intro x; cbn.
    snrapply path_sigma; cbn.
    + apply left_square.
    + refine (transport_sigma' _ _ @ _); cbn.
      apply path_sigma_hprop; cbn; symmetry.
      apply iscomplex_abses.
  - reflexivity.
Defined.

(** The original map factors via the induced map. *)
Definition abses_pullback_morphism_corec_beta `{Funext} {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : f = absesmorphism_compose (abses_pullback_morphism F (component3 f))
                              (abses_pullback_morphism_corec f).
Proof.
  apply (equiv_ap issig_AbSESMorphism^-1 _ _).
  srapply path_sigma_hprop.
  1: apply path_prod.
  1: apply path_prod.
  all: by apply equiv_path_grouphomomorphism.
Defined.

(** ** Pushouts of short exact sequences *)

Definition abses_pushout `{Univalence} {A A' B : AbGroup} (E : AbSES B A) (f : A $-> A')
  : AbSES B A'.
Proof.
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
      assert (bc : merely (hfiber grp_quotient_map bc'))
        by apply issurj_class_of.
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

Definition abses_pushout_morphism `{Univalence} {A A' B : AbGroup}
           (E : AbSES B A) (f : A $-> A')
  : AbSESMorphism E (abses_pushout E f).
Proof.
  snrapply (Build_AbSESMorphism f _ grp_homo_id).
  - exact ab_pushout_inr.
  - exact ab_pushout_commsq.
  - rapply ab_pushout_rec_beta_right.
Defined.

(** *** The universal property of [abses_pushout_morphism] *)

(* Any map [f : E -> F] of short exact sequences factors (uniquely) through [abses_pushout E f1]. *)

Definition abses_pushout_morphism_rec `{Univalence} {A B X Y : AbGroup}
           {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : AbSESMorphism (abses_pushout E (component1 f)) F.
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

(** ** The Baer sum of short exact sequences *)

(** Biproducts preserve exactness. *)
Lemma ab_biprod_exact {A E B X F Y : AbGroup}
      (i : A $-> E) (p : E $-> B) `{ex0 : IsExact (Tr (-1)) _ _ _ i p}
      (j : X $-> F) (q : F $-> Y) `{ex1 : IsExact (Tr (-1)) _ _ _ j q}
  : IsExact (Tr (-1)) (functor_ab_biprod i j)
            (functor_ab_biprod p q).
Proof.
  snrapply Build_IsExact.
  - snrapply Build_pHomotopy.
    + intro x; apply path_prod; cbn.
      * apply ex0.
      * apply ex1.
    + apply path_ishprop.
  - intros [ef u]; cbn.
    rapply contr_inhabited_hprop.
    destruct ef as [e f].
    pose (U := (equiv_path_prod _ _)^-1 u); cbn in U.
    pose proof (a := isexact_preimage _ i p e (fst U)).
    pose proof (x := isexact_preimage _ j q f (snd U)).
    strip_truncations; apply tr.
    exists (ab_biprod_inl a.1 + ab_biprod_inr x.1); cbn.
    apply path_sigma_hprop; cbn.
    apply path_prod; cbn.
    + rewrite right_identity.
      exact a.2.
    + rewrite left_identity.
      exact x.2.
Defined.

(** The pointwise direct sum of two short exact sequences. *)
Definition abses_direct_sum `{Univalence} {B A : AbGroup} (E F : AbSES B A)
  : AbSES (ab_biprod B B) (ab_biprod A A)
  := Build_AbSES (ab_biprod E F)
                 (functor_ab_biprod (inclusion E) (inclusion F))
                 (functor_ab_biprod (projection E) (projection F))
                 (functor_ab_biprod_embedding _ _)
                 (functor_ab_biprod_sujection _ _)
                 (ab_biprod_exact _ _ _ _).

(** The Baer sum of two short exact sequences is obtained from the pointwise direct sum by pushing forth along the codiagonal and then pulling back along the diagonal. (Swapping the order of pushing forth and pulling back produces an isomorphic short exact sequence.) *)
Definition abses_baer_sum `{Univalence} {B A : AbGroup} (E F : AbSES B A)
  : AbSES B A
  := abses_pullback (abses_pushout (abses_direct_sum E F) ab_codiagonal) ab_diagonal.


(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup) := Tr 0 (AbSES B A).

Global Instance ispointed_ext {B A : AbGroup} : IsPointed (Ext B A) := tr (point _).

(** An extension [E : AbSES B A] is trivial in [Ext B A] if and only if [E] merely splits. *)
Proposition iff_ab_ext_trivial_split `{Univalence} {B A : AbGroup} (E : AbSES B A)
  : merely {s : GroupHomomorphism B E & (projection _) $o s == idmap}
           <~> (tr E = point (Ext B A)).
Proof.
  refine (equiv_path_Tr _ _ oE _).
  srapply equiv_iff_hprop;
    apply Trunc_functor;
    apply iff_abses_trivial_split.
Defined.
