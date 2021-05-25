Require Import HoTT.Basics HoTT.Types HSet.
Require Import Groups AbGroups.AbelianGroup WildCat.
Require Import Homotopy.ExactSequence Pointed.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * Extensions of abelian groups *)

(** The type of abelian group extensions [A -> E -> B]. *)
Record hExt (B A : AbGroup) : Type := {
  hext_E : AbGroup;
  hext_i : A $-> hext_E;
  hext_p : hext_E $-> B;
  hext_isembedding_i : IsEmbedding hext_i;
  hext_issurjection_p : IsSurjection hext_p;
  hext_isexact : IsExact (Tr (-1)) hext_i hext_p;
}.

(** Given an extension [A -> E -> B : hExt B A], we coerce it to [E]. *)
Coercion hext_E : hExt >-> AbGroup.

Global Existing Instances hext_isembedding_i hext_issurjection_p hext_isexact.

Arguments hext_E {B A E} : rename.
Arguments hext_i {B A E} : rename.
Arguments hext_p {B A E} : rename.

Arguments Build_hExt {B A} _ _ _ _ _ _.

(** TODO Figure out why printing this term eats memory and seems to never finish. *)
Local Definition issig_hext_do_not_print {B A : AbGroup} : _ <~> hExt B A := ltac:(issig).

(** [make_equiv] is slow if used in the context of the next result, so we give the abstract form of the goal here. *)
Local Definition issig_hext_helper {AG : Type} {P : AG -> Type} {Q : AG -> Type}
           {R : forall E, P E -> Type} {S : forall E, Q E -> Type} {T : forall E, P E -> Q E -> Type}
  : {X : {E : AG & P E * Q E} & R _ (fst X.2) * S _ (snd X.2) * T _ (fst X.2) (snd X.2)}
  <~> {E : AG & {H0 : P E & {H1 : Q E & {_ : R _ H0 & {_ : S _ H1 & T _ H0 H1}}}}}
  := ltac:(make_equiv).

(** A more useful organization of [hExt] as a sigma-type. *)
Definition issig_hext {B A : AbGroup}
  : {X : {E : AbGroup & (A $-> E) * (E $-> B)} &
          (IsEmbedding (fst X.2)
           * IsSurjection (snd X.2)
           * IsExact (Tr (-1)) (fst X.2) (snd X.2))}
      <~> hExt B A
  := issig_hext_do_not_print oE issig_hext_helper.

(** [hExt B A] is pointed by the split sequence [A -> A+B -> B]. *)
Global Instance ispointed_hext {B A : AbGroup} : IsPointed (hExt B A).
Proof.
  rapply (Build_hExt (ab_biprod A B) ab_biprod_inl ab_biprod_pr2).
  snrapply Build_IsExact.
  - srapply Build_pHomotopy.
    + reflexivity.
    + apply path_ishprop.
  - intros [[a b] p]; cbn; cbn in p.
    rapply contr_inhabited_hprop.
    apply tr.
    exists a.
    rapply path_sigma_hprop; cbn.
    + intro x.
      apply istrunc_paths.
      exact _.
    + exact (path_prod' idpath p^).
Defined.

(** Paths in [hExt] corespond to isomorphisms between the [hext_E]s respecting [hext_i] and [hext_i]. *)
Proposition equiv_path_hext `{Univalence} {B A : AbGroup} (E F : hExt B A)
  : (E = F :> hExt B A)
      <~> {phi : GroupIsomorphism E F &
                 (phi $o hext_i = hext_i)
                 * (hext_p $o grp_iso_inverse phi = hext_p)}.
Proof.
  refine (_ oE equiv_ap issig_hext^-1 _ _).
  refine (_ oE (equiv_path_sigma_hprop _ _)^-1).
  refine (_ oE (equiv_path_sigma _ _ _)^-1).
  srapply equiv_functor_sigma'.
  1: exact equiv_path_abgroup^-1%equiv.
  intro q; lazy beta.
  snrefine (_ oE equiv_concat_l _ _); only 3: symmetry.
  2: exact (grp_homo_compose (equiv_path_abgroup^-1 q) hext_i,
            (grp_homo_compose hext_p (grp_iso_inverse (equiv_path_abgroup^-1 q)))).
  1: exact (equiv_path_prod _ _)^-1%equiv.
  refine (transport_prod _ _ @ _).
  apply path_prod'.
  - apply transport_abgrouphomomorphism_from_const.
  - apply transport_abgrouphomomorphism_to_const.
Defined.


(** * Characterization of trivial extensions

    We characterize trivial extensions in [hExt] as those for which [hext_p] splits. *)

(** If [hext_p : E -> B] splits, we get an induced map [fun e => e - s(hext_p s)] from [E] to [ab_kernel hext_p]. *)
Definition hext_p_split_to_kernel {B A : AbGroup} (E : hExt B A)
      {s : GroupHomomorphism B E} (h : hext_p $o s == idmap)
  : GroupHomomorphism E (@ab_kernel E B hext_p).
Proof.
  snrapply (grp_kernel_corec (G:=E) (A:=E)).
  - (** We construct the map [fun e => e - s(hext_p e)] by going via [E + E]. *)
    rapply grp_homo_compose.
    (** [fun e => (e,-e)] *)
    1: exact (ab_biprod_rec grp_homo_id ab_homo_negation).
    (** [fun (e,f) => e + s(hext_p s)] **)
    refine (ab_biprod_corec grp_homo_id (s $o hext_p)).
  - intro x; simpl.
    refine (grp_homo_op hext_p x _ @ _).
    refine (ap (fun y => hext_p x + y) _ @ right_inverse (hext_p x)).
    refine (grp_homo_inv _ _ @ ap (-) _ ).
    apply h.
Defined.

(** The composite [A -> E -> (ab_kernel hext_p) + B] is [grp_cxfib]. *)
Lemma hext_p_split_to_kernel_beta {B A : AbGroup} (E : hExt B A)
      {s : GroupHomomorphism B E} (h : hext_p $o s == idmap)
  : hext_p_split_to_kernel E h $o hext_i == grp_cxfib cx_isexact.
Proof.
  intro a.
  apply path_sigma_hprop; cbn.
  refine (ap _ _ @ right_identity (hext_i a)).
  refine (ap (fun x => - s x) _ @ _).
  1: rapply cx_isexact.
  exact (ap _ (grp_homo_unit _) @ negate_mon_unit).
Defined.

(** The induced map [E -> ab_kernel hext_p + B] is an isomorphism. We suffix it with 1 since it is the first composite in the desired isomorphism [E -> A + B]. *)
Definition hext_p_split_iso1 {B A : AbGroup} (E : hExt B A)
      {s : GroupHomomorphism B E} (h : hext_p $o s == idmap)
  : GroupIsomorphism E (ab_biprod (@ab_kernel E B hext_p) B).
Proof.
  srapply Build_GroupIsomorphism.
  - refine (ab_biprod_corec _ hext_p).
    exact (hext_p_split_to_kernel E h).
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
        refine (grp_homo_op (s $o hext_p) _ _ @ _).
        refine (ap (fun x => x + _) (ap s a.2 @ grp_homo_unit s) @ _).
        exact (left_identity _ @ ap s (h b)).
      * refine (grp_homo_op hext_p a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
    + intro e; simpl.
      by apply grp_moveR_gM.
Defined.

(** The full isomorphism [E -> A + B]. *)
Definition hext_p_split_iso {B A : AbGroup} (E : hExt B A)
      {s : GroupHomomorphism B E} (h : hext_p $o s == idmap)
  : GroupIsomorphism E (ab_biprod A B).
Proof.
  etransitivity (ab_biprod (ab_kernel _) B).
  - exact (hext_p_split_iso1 E h).
  - srapply (equiv_functor_ab_biprod (grp_iso_inverse _) grp_iso_id).
    rapply grp_iso_cxfib.
Defined.

Proposition hext_p_split_beta `{Funext} {B A : AbGroup} (E : hExt B A)
      {s : GroupHomomorphism B E} (h : hext_p $o s == idmap)
  : hext_p_split_iso E h $o hext_i == ab_biprod_inl.
Proof.
  intro a.
  refine (ap _ (ab_corec_beta _ _ _ _) @ _).
  refine (ab_biprod_functor_beta _ _ _ _ _ @ _).
  srefine (ap (fun p => ab_biprod_corec p _ a) _ @ _).
  1: exact grp_homo_id.
  - refine (ap (fun g => _ $o g) _ @ _);
      apply equiv_path_grouphomomorphism; intro.
    1: apply hext_p_split_to_kernel_beta.
    apply eissect.
  - refine (path_prod' idpath _); cbn.
    rapply cx_isexact.
Defined.

(** An extension [E] in [hExt B A] is trivial if and only if it splits. *)
Proposition iff_hext_trivial_split `{Univalence} {B A : AbGroup} (E : hExt B A)
  : (E = point _ :> hExt B A)
      <-> {s : GroupHomomorphism B E & hext_p $o s == idmap}.
Proof.
  refine (iff_compose (iff_equiv (equiv_path_hext _ _)) _); split.
  - intros [phi [g h]].
    exists (grp_homo_compose (grp_iso_inverse phi) ab_biprod_inr).
    intro x.
    exact (equiv_path_grouphomomorphism^-1 h (ab_biprod_inr x)).
  - intros [s h].
    exists (hext_p_split_iso E h).
    split; apply equiv_path_grouphomomorphism.
    + apply hext_p_split_beta.
    + intros [a b]; simpl.
      refine (grp_homo_op hext_p  _ _ @ _).
      refine (ap011 (+) _ (h _) @ _).
      1: rapply cx_isexact.
      apply left_identity.
Defined.


(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup) := Tr 0 (hExt B A).

Global Instance ispointed_ext {B A : AbGroup} : IsPointed (Ext B A) := tr (point _).
      
(** An extension [E : hext B A] is trivial in [Ext B A] if and only if [E] merely splits. *)
Proposition iff_ab_ext_trivial_split `{Univalence} {B A : AbGroup} (E : hExt B A)
  : (tr E = point (Ext B A))
      <~> merely { s : GroupHomomorphism B E & hext_p $o s == idmap }.
Proof.
  refine (_ oE (equiv_path_Tr _ _)^-1).
  srapply equiv_iff_hprop;
    apply Trunc_functor;
    apply iff_hext_trivial_split.
Defined.
