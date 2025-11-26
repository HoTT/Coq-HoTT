From HoTT Require Import Basics Types Truncations.Core.
Require Import WildCat Pointed.Core Homotopy.ExactSequence HIT.epi.
Require Import Modalities.ReflectiveSubuniverse.
Require Import AbelianGroup AbPushout AbHom AbGroups.Biproduct.
Require Import AbSES.Core AbSES.DirectSum.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope path_scope.
Local Open Scope mc_add_scope.

(** * Pushouts of short exact sequences *)

Definition abses_pushout `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : AbSES B A -> AbSES B A'.
Proof.
  intro E.
  snapply (Build_AbSES (ab_pushout f (inclusion E))
                        ab_pushout_inl
                        (ab_pushout_rec grp_homo_const (projection E) _)).
  - symmetry; rapply iscomplex_abses.
  - rapply ab_pushout_embedding_inl.
  - napply (cancelR_issurjection ab_pushout_inr _).
    rapply (conn_map_homotopic _ (projection E)); symmetry.
    napply ab_pushout_rec_beta_right.
  - snapply Build_IsExact.
    + srapply phomotopy_homotopy_hset.
      napply ab_pushout_rec_beta_left.
    + intros [bc' p].
      rapply contr_inhabited_hprop.
      (** Pick a preimage under the quotient map. *)
      assert (bc : merely (hfiber grp_quotient_map bc')).
      1: apply center, issurj_class_of.
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
        by rewrite involutive.
      * exact ((preserves_inverse a) @ ap _ s @ (right_identity _)^).
Defined.

(** ** The universal property of [abses_pushout_morphism] *)

Definition abses_pushout_morphism `{Univalence} {A A' B : AbGroup}
  (E : AbSES B A) (f : A $-> A')
  : AbSESMorphism E (abses_pushout f E).
Proof.
  snapply (Build_AbSESMorphism f _ grp_homo_id).
  - exact ab_pushout_inr.
  - exact ab_pushout_commsq.
  - rapply ab_pushout_rec_beta_right.
Defined.

(** Any map [f : E -> F] of short exact sequences factors (uniquely) through [abses_pushout E f1]. *)

Definition abses_pushout_morphism_rec `{Univalence} {A B X Y : AbGroup}
  {E : AbSES B A} {F : AbSES Y X} (f : AbSESMorphism E F)
  : AbSESMorphism (abses_pushout (component1 f) E) F.
Proof.
  snapply (Build_AbSESMorphism grp_homo_id _ (component3 f)).
  - rapply ab_pushout_rec.
    apply left_square.
  - intro x; simpl.
    rewrite grp_homo_unit.
    exact (right_identity _)^.
  - snapply (issurj_isepi_funext grp_quotient_map).
    1: apply issurj_class_of.
    2: exact _.
    intro x; simpl.
    napply grp_homo_op_agree.
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

(** Given [E : AbSES B A'] and [F : AbSES B A] and a morphism [f : E -> F], the pushout of [E] along [f_1] is [F] if [f_3] is homotopic to [id_B]. *)
Lemma abses_pushout_component3_id' `{Univalence}
  {A A' B : AbGroup} {E : AbSES B A'} {F : AbSES B A}
  (f : AbSESMorphism E F) (h : component3 f == grp_homo_id)
  : abses_pushout (component1 f) E $== F.
Proof.
  pose (g := abses_pushout_morphism_rec f).
  napply abses_path_data_to_iso.
  exists (component2 g); split.
  + intro x.
    exact (left_square g _)^.
  + intro x.
    exact ((right_square g _) @ h _)^.
Defined.

(** A version with equality instead of path data. *)
Definition abses_pushout_component3_id `{Univalence}
  {A A' B : AbGroup} {E : AbSES B A'} {F : AbSES B A}
  (f : AbSESMorphism E F) (h : component3 f == grp_homo_id)
  : abses_pushout (component1 f) E = F
  := equiv_path_abses_iso (abses_pushout_component3_id' f h).

(** Given short exact sequences [E] and [F] and homomorphisms [f : A' $-> A] and [g : D' $-> D], there is a morphism [E + F -> fE + gF] induced by the universal properties of the pushouts of [E] and [F]. *)
Definition abses_directsum_pushout_morphism `{Univalence}
  {A A' B C D D' : AbGroup} {E : AbSES B A'} {F : AbSES C D'}
  (f : A' $-> A) (g : D' $-> D)
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum (abses_pushout f E) (abses_pushout g F))
  := functor_abses_directsum (abses_pushout_morphism E f) (abses_pushout_morphism F g).

(** For [E, F : AbSES B A'] and [f, g : A' $-> A], we have (f+g)(E+F) = fE + gF, where + denotes the direct sum. *)
Definition abses_directsum_distributive_pushouts `{Univalence}
  {A A' B C C' D : AbGroup} {E : AbSES B A'} {F : AbSES D C'} (f : A' $-> A) (g : C' $-> C)
  : abses_pushout (functor_ab_biprod f g) (abses_direct_sum E F)
    = abses_direct_sum (abses_pushout f E) (abses_pushout g F)
  := abses_pushout_component3_id (abses_directsum_pushout_morphism f g) (fun _ => idpath).

(** Given an [AbSESMorphism] whose third component is the identity, we know that it induces a path from the pushout of the domain along the first map to the codomain. Conversely, given a path from a pushout, we can deduce that the following square commutes: *)
Definition abses_path_pushout_inclusion_commsq `{Univalence} {A A' B : AbGroup}
  (alpha : A $-> A') (E : AbSES B A) (F : AbSES B A')
  (p : abses_pushout alpha E = F)
  : exists phi : middle E $-> F, inclusion F o alpha == phi o inclusion E.
Proof.
  induction p.
  exists ab_pushout_inr; intro x.
  napply ab_pushout_commsq.
Defined.

(** ** Functoriality of [abses_pushout f : AbSES B A -> AbSES B A'] *)

(** In this file we will prove various "levels" of functoriality of pushing out. Here we show that the induced map between [AbSES B A] respect the groupoid structure of [is1gpd_abses] from AbSES.Core. *)

Instance is0functor_abses_pushout `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : Is0Functor (abses_pushout (B:=B) f).
Proof.
  srapply Build_Is0Functor;
    intros E F p.
  srapply abses_path_data_to_iso.
  srefine (functor_ab_pushout f f (inclusion _) (inclusion _) grp_homo_id grp_homo_id p.1 _ _; (_, _)).
  - reflexivity.
  - symmetry; exact (fst p.2).
  - napply ab_pushout_rec_beta_left.
  - srapply Quotient_ind_hprop.
    intro x; simpl.
    apply grp_cancelL.
    refine (snd p.2 (snd x) @ ap (projection F) _).
    exact (left_identity _)^.
Defined.

Instance is1functor_abses_pushout `{Univalence}
  {A A' B : AbGroup} (f : A $-> A')
  : Is1Functor (abses_pushout (B:=B) f).
Proof.
  srapply Build_Is1Functor.
  - intros E F g0 g1 h.
    rapply Quotient_ind_hprop; intros [a' e]; simpl.
    by rewrite (h e).
  - intro E.
    rapply Quotient_ind_hprop; intros [a' e]; simpl.
    refine (ap (class_of _) (path_prod' _ _)).
    + exact (grp_unit_r _).
    + exact (grp_unit_l _).
  - intros E F G g0 g1.
    rapply Quotient_ind_hprop; intros [a' e]; simpl.
    refine (ap (class_of _) (path_prod' _ _)).
    + exact (grp_unit_r _)^.
    + exact (ap (fun x => _ + g1.1 x) (grp_unit_l _)^).
Defined.

Definition abses_pushout_path_data_1 `{Univalence} {A A' B : AbGroup} (f : A $-> A') {E : AbSES B A} 
  : fmap (abses_pushout f) (Id E) = Id (abses_pushout f E).
Proof.
  srapply path_sigma_hprop.
  apply equiv_path_groupisomorphism.
  srapply Quotient_ind_hprop.
  intros [a' e]; simpl. (* This is true even on the representatives. *)
  apply qglue.
  refine (tr (0; _)).
  apply path_prod'; cbn.
  - refine (ap _ (grp_homo_unit _) @ _).
    refine (grp_inv_unit @ _).
    apply grp_moveL_Vg.
    exact (right_identity _ @ right_identity _).
  - refine (grp_homo_unit _ @ _).
    apply grp_moveL_Vg.
    exact (right_identity _ @ left_identity _).
Defined.

Definition ap_abses_pushout `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  {E F : AbSES B A} (p : E = F)
  : ap (abses_pushout f) p
    = equiv_path_abses_iso (fmap (abses_pushout f) (equiv_path_abses_iso^-1 p)).
Proof.
  induction p.
  refine (_ @ ap _ _).
  2: exact ((abses_pushout_path_data_1 f)^ @ ap _ equiv_path_absesV_1^).
  exact equiv_path_abses_1^.
Defined.

Definition ap_abses_pushout_data `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  {E F : AbSES B A} (p : E $== F)
  : ap (abses_pushout f) (equiv_path_abses_iso p)
    = equiv_path_abses_iso (fmap (abses_pushout f) p).
Proof.
  refine (ap_abses_pushout _ _ @ _).
  apply (ap (equiv_path_abses_iso o _)).
  apply eissect.
Defined.

Definition abses_pushout_point' `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : abses_pushout f (point (AbSES B A)) $== pt.
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
  : abses_pushout f (point (AbSES B A)) = pt
  := equiv_path_abses_iso (abses_pushout_point' f).

Definition abses_pushout' `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : AbSES B A -->* AbSES B A'
  := Build_BasepointPreservingFunctor (abses_pushout f) (abses_pushout_point' f).

Definition abses_pushout_pmap `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : AbSES B A ->* AbSES B A'
  := to_pointed (abses_pushout' f).

(** The following general lemma lets us show that [abses_pushout f E] is trivial in cases of interest. It says that if you have a map [phi : E -> A'], then if you push out along the restriction [phi $o inclusion E], the result is trivial. Specifically, we get a morphism witnessing this fact.  *)
Definition abses_pushout_trivial_morphism {B A A' : AbGroup}
  (E : AbSES B A) (f : A $-> A') (phi : middle E $-> A')
  (k : f == phi $o inclusion E)
  : AbSESMorphism E (pt : AbSES B A').
Proof.
  srapply (Build_AbSESMorphism f _ grp_homo_id).
  1: exact (ab_biprod_corec phi (projection E)).
  { intro a; cbn.
    refine (path_prod' (k a) _^).
    apply isexact_inclusion_projection. }
  reflexivity.
Defined.

(** The pushout of a short exact sequence along its inclusion map is trivial. *)
Definition abses_pushout_inclusion_morphism {B A : AbGroup} (E : AbSES B A)
  : AbSESMorphism E (pt : AbSES B E)
  := abses_pushout_trivial_morphism E (inclusion E) grp_homo_id (fun _ => idpath).

Definition abses_pushout_inclusion `{Univalence} {B A : AbGroup} (E : AbSES B A)
  : abses_pushout (inclusion E) E = pt
  := abses_pushout_component3_id
       (abses_pushout_inclusion_morphism E) (fun _ => idpath).

(** Pushing out along [grp_homo_const] is trivial. *)
Definition abses_pushout_const_morphism {B A A' : AbGroup} (E : AbSES B A)
  : AbSESMorphism E (pt : AbSES B A')
  := abses_pushout_trivial_morphism E
       grp_homo_const grp_homo_const (fun _ => idpath).

Definition abses_pushout_const `{Univalence} {B A A' : AbGroup} (E : AbSES B A)
  : abses_pushout grp_homo_const E = pt :> AbSES B A'
  := abses_pushout_component3_id
       (abses_pushout_const_morphism E) (fun _ => idpath).

(** Pushing out a fixed extension, with the map variable. This is the connecting map in the contravariant six-term exact sequence (see SixTerm.v). *)
Definition abses_pushout_abses `{Univalence} {B A G : AbGroup} (E : AbSES B A)
  : ab_hom A G ->* AbSES B G.
Proof.
  srapply Build_pMap.
  1: exact (fun g => abses_pushout g E).
  apply abses_pushout_const.
Defined.

(** ** Functoriality of pushing out *)

(** For every [E : AbSES B A], the pushout of [E] along [id_A] is [E]. *)
Definition abses_pushout_id `{Univalence} {A B : AbGroup}
  : abses_pushout (B:=B) (@grp_homo_id A) == idmap
  := fun E => abses_pushout_component3_id (abses_morphism_id E) (fun _ => idpath).

Definition abses_pushout_pmap_id `{Univalence} {A B : AbGroup}
  : abses_pushout_pmap (B:=B) (@grp_homo_id A) ==* @pmap_idmap (AbSES B A).
Proof.
  srapply Build_pHomotopy.
  1: exact abses_pushout_id.
  refine (_ @ (concat_p1 _)^).
  (* For some reason Coq spends time finding [x] below, so we specify it. *)
  napply (ap equiv_path_abses_iso
             (x:=abses_pushout_component3_id' (abses_morphism_id pt) _)).
  apply path_sigma_hprop.
  apply equiv_path_groupisomorphism.
  by rapply Quotient_ind_hprop.
Defined.

(** Pushing out along homotopic maps induces homotopic pushout functors. This statement has a short proof by path induction on the homotopy [h], but we prefer to construct a path using [abses_path_data_iso] with better computational properties. *)
Lemma abses_pushout_homotopic' `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout (B:=B) f $=> abses_pushout f'.
Proof.
  intro E; cbn.
  apply abses_path_data_to_iso.
  snrefine (_; (_, _)).
  - srapply (ab_pushout_rec (inclusion _)).
    1: exact ab_pushout_inr.
    intro x.
    refine (ap _ (h x) @ _).
    exact (ab_pushout_commsq x).
  - apply ab_pushout_rec_beta_left.
  - rapply Quotient_ind_hprop; intros [a' e]; simpl.
    exact (ap (fun x => _ + projection E x) (grp_unit_l _)^).
Defined.

Definition abses_pushout_homotopic `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout (B:=B) f == abses_pushout f'
  := equiv_path_data_homotopy _ _ (abses_pushout_homotopic' _ _ h).

Definition abses_pushout_phomotopic' `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout' (B:=B) f $=>* abses_pushout' f'.
Proof.
  exists (abses_pushout_homotopic' _ _ h).
  apply gpd_moveL_Vh.
  rapply Quotient_ind_hprop; intros [a' [a b]]; simpl.
  apply path_prod'.
  - by rewrite grp_unit_l, grp_unit_r, (h a).
  - apply grp_unit_l.
Defined.

Definition abses_pushout_phomotopic `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout_pmap (B:=B) f ==* abses_pushout_pmap f'
  := equiv_ptransformation_phomotopy (abses_pushout_phomotopic' f f' h).

Definition abses_pushout_compose' `{Univalence} {A0 A1 A2 B : AbGroup}
  (f : A0 $-> A1) (g : A1 $-> A2)
  : abses_pushout (g $o f) $=> abses_pushout (B:=B) g o abses_pushout f.
Proof.
  intro E.
  srapply abses_path_data_to_iso;
    srefine (_; (_,_)).
  - snapply ab_pushout_rec.
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
  : abses_pushout (g $o f) == abses_pushout (B:=B) g o abses_pushout f
  := equiv_path_data_homotopy _ _ (abses_pushout_compose' f g).

Definition abses_pushout_pcompose' `{Univalence} {A0 A1 A2 B : AbGroup}
  (f : A0 $-> A1) (g : A1 $-> A2)
  : abses_pushout' (B:=B) (g $o f) $=>* abses_pushout' g $o* abses_pushout' f.
Proof.
  exists (abses_pushout_compose' f g).
  apply gpd_moveL_Vh. (* it's easiest to construct a path in [pt] *)
  rapply Quotient_ind_hprop; intros [a2 [a0 b]]; simpl.
  by rewrite 7 grp_unit_l, 2 grp_unit_r.
Defined.

Definition abses_pushout_pcompose `{Univalence} {A0 A1 A2 B : AbGroup}
  (f : A0 $-> A1) (g : A1 $-> A2)
  : abses_pushout_pmap (B:=B) (g $o f)
      ==* abses_pushout_pmap g o* abses_pushout_pmap f.
Proof.
  refine (_ @* (to_pointed_compose _ _)^*).
  apply equiv_ptransformation_phomotopy.
  apply abses_pushout_pcompose'.
Defined.

(** [AbSES B : AbGroup -> pType] and [AbSES' B : AbGroup -> Type] are covariant functors, for any [B]. *)

Instance is0functor_abses'01 `{Univalence} {B : AbGroup^op}
  : Is0Functor (AbSES' B).
Proof.
  apply Build_Is0Functor.
  exact (fun _ _ g => abses_pushout g).
Defined.

Instance is1functor_abses'01 `{Univalence} {B : AbGroup^op}
  : Is1Functor (AbSES' B).
Proof.
  apply Build_Is1Functor; intros; cbn.
  - by apply abses_pushout_homotopic.
  - exact abses_pushout_id.
  - apply abses_pushout_compose.
Defined.

Instance is0functor_abses01 `{Univalence} {B : AbGroup^op}
  : Is0Functor (AbSES B).
Proof.
  apply Build_Is0Functor.
  exact (fun _ _ g => abses_pushout_pmap g).
Defined.

Instance is1functor_abses01 `{Univalence} {B : AbGroup^op}
  : Is1Functor (AbSES B).
Proof.
  apply Build_Is1Functor; intros; cbn.
  - by apply abses_pushout_phomotopic.
  - apply abses_pushout_pmap_id.
  - apply abses_pushout_pcompose.
Defined.
