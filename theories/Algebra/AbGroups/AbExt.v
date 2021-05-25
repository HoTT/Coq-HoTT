Require Import HoTT.Basics HoTT.Types HSet.
Require Import Groups AbGroups.AbelianGroup WildCat.
Require Import Homotopy.ExactSequence Pointed.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * Extensions of abelian groups *)

(** The type of abelian group extensions [A -> E -> B]. *)
Record AbExt (B A : AbGroup) : Type := {
  abext_E : AbGroup;
  abext_i : A $-> abext_E;
  abext_p : abext_E $-> B;
  abext_isembedding_i : IsEmbedding abext_i;
  abext_issurjection_p : IsSurjection abext_p;
  abext_isexact : IsExact (Tr (-1)) abext_i abext_p;
}.

(** Given an extension [A -> E -> B : AbExt B A], we coerce it to [E]. *)
Coercion abext_E : AbExt >-> AbGroup.

Global Existing Instances abext_isembedding_i abext_issurjection_p abext_isexact.

Arguments abext_E {B A E} : rename.
Arguments abext_i {B A E} : rename.
Arguments abext_p {B A E} : rename.

Arguments Build_AbExt {B A} _ _ _ _ _ _.

(** TODO Figure out why printing this term eats memory and seems to never finish. *)
Local Definition issig_abext_do_not_print {B A : AbGroup} : _ <~> AbExt B A := ltac:(issig).

(** [make_equiv] is slow if used in the context of the next result, so we give the abstract form of the goal here. *)
Local Definition issig_abext_helper {AG : Type} {P : AG -> Type} {Q : AG -> Type}
           {R : forall E, P E -> Type} {S : forall E, Q E -> Type} {T : forall E, P E -> Q E -> Type}
  : {X : {E : AG & P E * Q E} & R _ (fst X.2) * S _ (snd X.2) * T _ (fst X.2) (snd X.2)}
  <~> {E : AG & {H0 : P E & {H1 : Q E & {_ : R _ H0 & {_ : S _ H1 & T _ H0 H1}}}}}
  := ltac:(make_equiv).

(** A more useful organization of [AbExt] as a sigma-type. *)
Definition issig_abext {B A : AbGroup}
  : {X : {E : AbGroup & (A $-> E) * (E $-> B)} &
          (IsEmbedding (fst X.2)
           * IsSurjection (snd X.2)
           * IsExact (Tr (-1)) (fst X.2) (snd X.2))}
      <~> AbExt B A
  := issig_abext_do_not_print oE issig_abext_helper.

(** [AbExt B A] is pointed by the split sequence [A -> A+B -> B]. *)
Global Instance ispointed_abext {B A : AbGroup} : IsPointed (AbExt B A).
Proof.
  rapply (Build_AbExt (ab_biprod A B) ab_biprod_inl ab_biprod_pr2).
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

(** Paths in [AbExt] corespond to isomorphisms between the [abext_E]s respecting [abext_i] and [abext_p]. *)
Proposition equiv_path_abext `{Univalence} {B A : AbGroup} (E F : AbExt B A)
  : (E = F) <~> {phi : GroupIsomorphism E F &
                       (phi $o abext_i = abext_i)
                       * (abext_p $o grp_iso_inverse phi = abext_p)}.
Proof.
  refine (_ oE equiv_ap issig_abext^-1 _ _).
  refine (_ oE (equiv_path_sigma_hprop _ _)^-1).
  refine (_ oE (equiv_path_sigma _ _ _)^-1).
  srapply equiv_functor_sigma'.
  1: exact equiv_path_abgroup^-1%equiv.
  intro q; lazy beta.
  snrefine (_ oE equiv_concat_l _ _); only 3: symmetry.
  2: exact (grp_homo_compose (equiv_path_abgroup^-1 q) abext_i,
            (grp_homo_compose abext_p (grp_iso_inverse (equiv_path_abgroup^-1 q)))).
  1: exact (equiv_path_prod _ _)^-1%equiv.
  refine (transport_prod _ _ @ _).
  apply path_prod'.
  - apply transport_abgrouphomomorphism_from_const.
  - apply transport_abgrouphomomorphism_to_const.
Defined.


(** * Characterization of trivial extensions

    We characterize trivial extensions in [AbExt] as those for which [abext_p] splits. *)

(** If [abext_p : E -> B] splits, we get an induced map [fun e => e - s (abext_p e)] from [E] to [ab_kernel abext_p]. *)
Definition abext_p_split_to_kernel {B A : AbGroup} (E : AbExt B A)
      {s : GroupHomomorphism B E} (h : abext_p $o s == idmap)
  : GroupHomomorphism E (@ab_kernel E B abext_p).
Proof.
  snrapply (grp_kernel_corec (G:=E) (A:=E)).
  - exact (ab_homo_add grp_homo_id (ab_homo_negation $o s $o abext_p)).
  - intro x; simpl.
    refine (grp_homo_op abext_p x _ @ _).
    refine (ap (fun y => abext_p x + y) _ @ right_inverse (abext_p x)).
    refine (grp_homo_inv _ _ @ ap (-) _ ).
    apply h.
Defined.

(** The composite [A -> E -> ab_kernel abext_p] is [grp_cxfib]. *)
Lemma abext_p_split_to_kernel_beta {B A : AbGroup} (E : AbExt B A)
      {s : GroupHomomorphism B E} (h : abext_p $o s == idmap)
  : abext_p_split_to_kernel E h $o abext_i == grp_cxfib cx_isexact.
Proof.
  intro a.
  apply path_sigma_hprop; cbn.
  apply grp_cancelL1.
  refine (ap (fun x => - s x) _ @ _).
  1: rapply cx_isexact.
  exact (ap _ (grp_homo_unit _) @ negate_mon_unit).
Defined.

(** The induced map [E -> ab_kernel abext_p + B] is an isomorphism. We suffix it with 1 since it is the first composite in the desired isomorphism [E -> A + B]. *)
Definition abext_p_split_iso1 {B A : AbGroup} (E : AbExt B A)
      {s : GroupHomomorphism B E} (h : abext_p $o s == idmap)
  : GroupIsomorphism E (ab_biprod (@ab_kernel E B abext_p) B).
Proof.
  srapply Build_GroupIsomorphism.
  - refine (ab_biprod_corec _ abext_p).
    exact (abext_p_split_to_kernel E h).
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
        refine (grp_homo_op abext_p a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
      * refine (grp_homo_op abext_p a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
    + intro e; simpl.
      by apply grp_moveR_gM.
Defined.

(** The full isomorphism [E -> A+B]. *)
Definition abext_p_split_iso {B A : AbGroup} (E : AbExt B A)
      {s : GroupHomomorphism B E} (h : abext_p $o s == idmap)
  : GroupIsomorphism E (ab_biprod A B).
Proof.
  etransitivity (ab_biprod (ab_kernel _) B).
  - exact (abext_p_split_iso1 E h).
  - srapply (equiv_functor_ab_biprod (grp_iso_inverse _) grp_iso_id).
    rapply grp_iso_cxfib.
Defined.

Proposition abext_p_split_beta {B A : AbGroup} (E : AbExt B A)
      {s : GroupHomomorphism B E} (h : abext_p $o s == idmap)
  : abext_p_split_iso E h $o abext_i == ab_biprod_inl.
Proof.
  intro a.
  refine (ap _ (ab_corec_beta _ _ _ _) @ _).
  refine (ab_biprod_functor_beta _ _ _ _ _ @ _).
  nrapply path_prod'.
  2: rapply cx_isexact.
  refine (ap _ (abext_p_split_to_kernel_beta E h a) @ _).
  apply eissect.
Defined.

(** An extension [E] in [AbExt B A] is trivial if and only if it splits. *)
Proposition iff_abext_trivial_split `{Univalence} {B A : AbGroup} (E : AbExt B A)
  : (E = point (AbExt B A))
      <-> {s : GroupHomomorphism B E & abext_p $o s == idmap}.
Proof.
  refine (iff_compose (iff_equiv (equiv_path_abext _ _)) _); split.
  - intros [phi [g h]].
    exists (grp_homo_compose (grp_iso_inverse phi) ab_biprod_inr).
    intro x.
    exact (equiv_path_grouphomomorphism^-1 h (ab_biprod_inr x)).
  - intros [s h].
    exists (abext_p_split_iso E h).
    split; apply equiv_path_grouphomomorphism.
    + apply abext_p_split_beta.
    + intros [a b]; simpl.
      refine (grp_homo_op abext_p  _ _ @ _).
      refine (ap011 (+) _ (h _) @ _).
      1: rapply cx_isexact.
      apply left_identity.
Defined.


(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup) := Tr 0 (AbExt B A).

Global Instance ispointed_ext {B A : AbGroup} : IsPointed (Ext B A) := tr (point _).
      
(** An extension [E : AbExt B A] is trivial in [Ext B A] if and only if [E] merely splits. *)
Proposition iff_ab_ext_trivial_split `{Univalence} {B A : AbGroup} (E : AbExt B A)
  : (tr E = point (Ext B A))
      <~> merely { s : GroupHomomorphism B E & abext_p $o s == idmap }.
Proof.
  refine (_ oE (equiv_path_Tr _ _)^-1).
  srapply equiv_iff_hprop;
    apply Trunc_functor;
    apply iff_abext_trivial_split.
Defined.
