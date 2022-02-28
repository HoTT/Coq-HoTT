Require Import HoTT.Basics HoTT.Types HSet.
Require Import Groups AbGroups.AbelianGroup AbGroups.AbPullback WildCat.
Require Import Homotopy.ExactSequence Pointed HFiber Limits.Pullback.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * Short exact sequences of abelian groups *)

(** A short exact sequence of abelian groups consists of a monomorphism [i : A -> E] and an epimorphism [p : E -> B] such that the image of [i] equals the kernel of [p]. Later we will consider short exact sequences up to isomorphism by 0-truncating the type [AbSES] defined below. An isomorphism class of short exact sequences is called an extension. *)

(** The type of short exact sequences [A -> E -> B] of abelian groups. *)
Record AbSES (B A : AbGroup) : Type := {
  abses_E : AbGroup;
  abses_i : A $-> abses_E;
  abses_p : abses_E $-> B;
  abses_isembedding_i : IsEmbedding abses_i;
  abses_issurjection_p : IsSurjection abses_p;
  abses_isexact : IsExact (Tr (-1)) abses_i abses_p;
}.

(** Given a short exact sequence [A -> E -> B : AbSES B A], we coerce it to [E]. *)
Coercion abses_E : AbSES >-> AbGroup.

Global Existing Instances abses_isembedding_i abses_issurjection_p abses_isexact.

Arguments abses_E {B A} E : rename.
Arguments abses_i {B A} E : rename.
Arguments abses_p {B A} E : rename.
Arguments abses_isembedding_i {B A} E : rename.
Arguments abses_issurjection_p {B A} E : rename.
Arguments abses_isexact {B A} E : rename.

Arguments Build_AbSES {B A} _ _ _ _ _ _.

(** TODO Figure out why printing this term eats memory and seems to never finish. *)
Local Definition issig_abses_do_not_print {B A : AbGroup} : _ <~> AbSES B A := ltac:(issig).

(** [make_equiv] is slow if used in the context of the next result, so we give the abstract form of the goal here. *)
Local Definition issig_abses_helper {AG : Type} {P : AG -> Type} {Q : AG -> Type}
           {R : forall E, P E -> Type} {S : forall E, Q E -> Type} {T : forall E, P E -> Q E -> Type}
  : {X : {E : AG & P E * Q E} & R _ (fst X.2) * S _ (snd X.2) * T _ (fst X.2) (snd X.2)}
  <~> {E : AG & {H0 : P E & {H1 : Q E & {_ : R _ H0 & {_ : S _ H1 & T _ H0 H1}}}}}
  := ltac:(make_equiv).

(** A more useful organization of [AbSES] as a sigma-type. *)
Definition issig_abses {B A : AbGroup}
  : {X : {E : AbGroup & (A $-> E) * (E $-> B)} &
          (IsEmbedding (fst X.2)
           * IsSurjection (snd X.2)
           * IsExact (Tr (-1)) (fst X.2) (snd X.2))}
      <~> AbSES B A
  := issig_abses_do_not_print oE issig_abses_helper.

Definition iscomplex_abses {A B : AbGroup} (E : AbSES B A)
  : IsComplex (abses_i E) (abses_p E)
  := cx_isexact.

(** [AbSES B A] is pointed by the split sequence [A -> A+B -> B]. *)
Global Instance ispointed_abses {B A : AbGroup} : IsPointed (AbSES B A).
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

(** Paths in [AbSES] corespond to isomorphisms between the [abses_E]s respecting [abses_i] and [abses_p]. *)
Proposition equiv_path_abses `{Univalence} {B A : AbGroup} (E F : AbSES B A)
  : (E = F) <~> {phi : GroupIsomorphism E F &
                       (phi $o abses_i _ = abses_i _)
                       * (abses_p _ $o grp_iso_inverse phi = abses_p _)}.
Proof.
  refine (_ oE equiv_ap issig_abses^-1 _ _).
  refine (_ oE (equiv_path_sigma_hprop _ _)^-1).
  refine (_ oE (equiv_path_sigma _ _ _)^-1).
  srapply equiv_functor_sigma'.
  1: exact equiv_path_abgroup^-1%equiv.
  intro q; lazy beta.
  snrefine (_ oE equiv_concat_l _ _); only 3: symmetry.
  2: exact (grp_homo_compose (equiv_path_abgroup^-1 q) (abses_i _),
            (grp_homo_compose (abses_p _) (grp_iso_inverse (equiv_path_abgroup^-1 q)))).
  1: exact (equiv_path_prod _ _)^-1%equiv.
  refine (transport_prod _ _ @ _).
  apply path_prod'.
  - apply transport_abgrouphomomorphism_from_const.
  - apply transport_abgrouphomomorphism_to_const.
Defined.

(** ** Characterization of split short exact sequences

    We characterize trivial short exact sequences in [AbSES] as those for which [abses_p] splits. *)

(** If [abses_p : E -> B] splits, we get an induced map [fun e => e - s (abses_p e)] from [E] to [ab_kernel abses_p]. *)
Definition abses_p_split_to_kernel {B A : AbGroup} (E : AbSES B A)
      {s : GroupHomomorphism B E} (h : abses_p _ $o s == idmap)
  : GroupHomomorphism E (@ab_kernel E B (abses_p _)).
Proof.
  snrapply (grp_kernel_corec (G:=E) (A:=E)).
  - exact (ab_homo_add grp_homo_id (ab_homo_negation $o s $o (abses_p _))).
  - intro x; simpl.
    refine (grp_homo_op (abses_p _) x _ @ _).
    refine (ap (fun y => (abses_p _) x + y) _ @ right_inverse ((abses_p _) x)).
    refine (grp_homo_inv _ _ @ ap (-) _ ).
    apply h.
Defined.

(** The composite [A -> E -> ab_kernel abses_p] is [grp_cxfib]. *)
Lemma abses_p_split_to_kernel_beta {B A : AbGroup} (E : AbSES B A)
      {s : GroupHomomorphism B E} (h : (abses_p _) $o s == idmap)
  : abses_p_split_to_kernel E h $o (abses_i _) == grp_cxfib cx_isexact.
Proof.
  intro a.
  apply path_sigma_hprop; cbn.
  apply grp_cancelL1.
  refine (ap (fun x => - s x) _ @ _).
  1: rapply cx_isexact.
  exact (ap _ (grp_homo_unit _) @ negate_mon_unit).
Defined.

(** The induced map [E -> ab_kernel abses_p + B] is an isomorphism. We suffix it with 1 since it is the first composite in the desired isomorphism [E -> A + B]. *)
Definition abses_p_split_iso1 {B A : AbGroup} (E : AbSES B A)
      {s : GroupHomomorphism B E} (h : (abses_p _) $o s == idmap)
  : GroupIsomorphism E (ab_biprod (@ab_kernel E B (abses_p _)) B).
Proof.
  srapply Build_GroupIsomorphism.
  - refine (ab_biprod_corec _ (abses_p _)).
    exact (abses_p_split_to_kernel E h).
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
        refine (grp_homo_op (abses_p _) a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
      * refine (grp_homo_op (abses_p _) a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
    + intro e; simpl.
      by apply grp_moveR_gM.
Defined.

(** The full isomorphism [E -> A+B]. *)
Definition abses_p_split_iso {B A : AbGroup} (E : AbSES B A)
      {s : GroupHomomorphism B E} (h : (abses_p _) $o s == idmap)
  : GroupIsomorphism E (ab_biprod A B).
Proof.
  etransitivity (ab_biprod (ab_kernel _) B).
  - exact (abses_p_split_iso1 E h).
  - srapply (equiv_functor_ab_biprod (grp_iso_inverse _) grp_iso_id).
    rapply grp_iso_cxfib.
Defined.

Proposition abses_p_split_beta {B A : AbGroup} (E : AbSES B A)
      {s : GroupHomomorphism B E} (h : (abses_p _) $o s == idmap)
  : abses_p_split_iso E h $o (abses_i _) == ab_biprod_inl.
Proof.
  intro a.
  refine (ap _ (ab_corec_beta _ _ _ _) @ _).
  refine (ab_biprod_functor_beta _ _ _ _ _ @ _).
  nrapply path_prod'.
  2: rapply cx_isexact.
  refine (ap _ (abses_p_split_to_kernel_beta E h a) @ _).
  apply eissect.
Defined.

(** A short exact sequence [E] in [AbSES B A] is trivial if and only if [ab_ses p] splits. *)
Proposition iff_abses_trivial_split `{Univalence} {B A : AbGroup} (E : AbSES B A)
  : (E = point (AbSES B A))
      <-> {s : GroupHomomorphism B E & (abses_p _) $o s == idmap}.
Proof.
  refine (iff_compose (iff_equiv (equiv_path_abses _ _)) _); split.
  - intros [phi [g h]].
    exists (grp_homo_compose (grp_iso_inverse phi) ab_biprod_inr).
    intro x.
    exact (equiv_path_grouphomomorphism^-1 h (ab_biprod_inr x)).
  - intros [s h].
    exists (abses_p_split_iso E h).
    split; apply equiv_path_grouphomomorphism.
    + apply abses_p_split_beta.
    + intros [a b]; simpl.
      refine (grp_homo_op (abses_p _)  _ _ @ _).
      refine (ap011 (+) _ (h _) @ _).
      1: rapply cx_isexact.
      apply left_identity.
Defined.


(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup) := Tr 0 (AbSES B A).

Global Instance ispointed_ext {B A : AbGroup} : IsPointed (Ext B A) := tr (point _).

(** An extension [E : AbSES B A] is trivial in [Ext B A] if and only if [E] merely splits. *)
Proposition iff_ab_ext_trivial_split `{Univalence} {B A : AbGroup} (E : AbSES B A)
  : (tr E = point (Ext B A))
      <~> merely { s : GroupHomomorphism B E & (abses_p _) $o s == idmap }.
Proof.
  refine (_ oE (equiv_path_Tr _ _)^-1).
  srapply equiv_iff_hprop;
    apply Trunc_functor;
    apply iff_abses_trivial_split.
Defined.
