Require Import HoTT.Basics HoTT.Types HSet WildCat.
Require Import Groups AbGroups.AbelianGroup.
Require Import Homotopy.ExactSequence Pointed.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * Short exact sequences of abelian groups *)

(** A short exact sequence of abelian groups consists of a monomorphism [i : A -> E] and an epimorphism [p : E -> B] such that the image of [i] equals the kernel of [p]. Later we will consider short exact sequences up to isomorphism by 0-truncating the type [AbSES] defined below. An isomorphism class of short exact sequences is called an extension. *)

Declare Scope abses_scope.
Local Open Scope abses_scope.

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

(** ** Paths in [AbSES B A] *)

Definition abses_path_data_iso {B A : AbGroup} (E F : AbSES B A)
  := {phi : GroupIsomorphism E F
            & (phi $o inclusion _ == inclusion _)
              * (projection _ == projection _ $o phi)}.

(** Having the path data in a slightly different form is useful for [equiv_path_abses_iso]. *)
Local Lemma shuffle_abses_path_data_iso `{Funext} {B A : AbGroup} (E F : AbSES B A)
  : (abses_path_data_iso E F)
      <~> {phi : GroupIsomorphism E F
                 & (phi $o inclusion _ == inclusion _)
                   * (projection _ $o grp_iso_inverse phi == projection _)}.
Proof.
  srapply equiv_functor_sigma_id; intro phi.
  srapply equiv_functor_prod'.
  1: exact equiv_idmap.
  srapply (equiv_functor_forall' phi^-1); intro e; cbn.
  apply equiv_concat_r.
  exact (ap _ (eisretr _ _)).
Defined.

(** Paths in [AbSES] correspond to isomorphisms between the [middle]s respecting [inclusion] and [projection]. Below we prove the stronger statement [equiv_path_abses], which uses this result. *)
Proposition equiv_path_abses_iso `{Univalence} {B A : AbGroup} {E F : AbSES B A}
  : abses_path_data_iso E F <~> E = F.
Proof.
  refine (_ oE shuffle_abses_path_data_iso E F).
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

(** It follows that [AbSES B A] is 1-truncated. *)
Global Instance istrunc_abses `{Univalence} {B A : AbGroup} : IsTrunc 1 (AbSES B A).
Proof.
  intros E F.
  refine (istrunc_equiv_istrunc _ equiv_path_abses_iso (n:=0)).
  rapply istrunc_sigma.
  apply ishset_groupisomorphism.
Defined.

Definition path_abses_iso `{Univalence} {B A : AbGroup} {E F : AbSES B A}
           (phi : GroupIsomorphism E F) (p : phi $o inclusion _ == inclusion _)
           (q : projection _ == projection _ $o phi)
  : E = F := equiv_path_abses_iso (phi; (p,q)).

(** Given [p] and [q], the map [phi] just above is automatically an isomorphism. Showing this requires the "short five lemma." *)

(** A special case of the "short 5-lemma" where the two outer maps are (definitionally) identities. *)
Lemma short_five_lemma {B A : AbGroup} {E F : AbSES B A} (phi : GroupHomomorphism E F)
      (p0 : phi $o inclusion E == inclusion F) (p1 : projection E == projection F $o phi)
  : IsEquiv phi.
Proof.
  apply isequiv_surj_emb.
  - intro f.
    rapply contr_inhabited_hprop.
    (** Since [projection E] is epi, we can pull [projection F f] back to [e0 : E].*)
    assert (e0 : Tr (-1) (hfiber (projection E) (projection F f))).
    1: apply issurjection_projection.
    strip_truncations.
    (** The difference [f - (phi e0.1)] is sent to [0] by [projection F], hence lies in [A]. *)
    assert (a : Tr (-1) (hfiber (inclusion F) (f + (- phi e0.1)))).
    1: { refine (isexact_preimage (Tr (-1)) (inclusion F) (projection F) _ _).
         refine (grp_homo_op _ _ _ @ _).
         refine (ap _ (grp_homo_inv _ _) @ _).
         apply (grp_moveL_1M)^-1.
         exact (e0.2^ @ p1 e0.1). }
    strip_truncations.
    refine (tr (inclusion E a.1 + e0.1; _)).
    refine (grp_homo_op _ _ _ @ _).
    refine (ap (fun x => x + phi e0.1) (p0 a.1 @ a.2) @ _).
    refine ((grp_assoc _ _ _)^ @ _).
    refine (ap _ (left_inverse (phi e0.1)) @ _).
    apply grp_unit_r.
  - apply isembedding_grouphomomorphism.
    intros e p.
    assert (a : Tr (-1) (hfiber (inclusion E) e)).
    1: { refine (isexact_preimage _ (inclusion E) (projection E) _ _).
         exact (p1 e @ ap (projection F) p @ grp_homo_unit _). }
    strip_truncations.
    refine (a.2^ @ ap (inclusion E ) _ @ grp_homo_unit (inclusion E)).
    rapply (isinj_embedding (inclusion F) _ _).
    refine ((p0 a.1)^ @ (ap phi a.2) @ p @ (grp_homo_unit _)^).
Defined.

(** Below we prove that homomorphisms respecting [projection] and [inclusion] correspond to paths in [AbSES B A]. We refer to such homomorphisms simply as path data in [AbSES B A]. *)
Definition abses_path_data {B A : AbGroup} (E F : AbSES B A)
  := {phi : GroupHomomorphism E F
            & (phi $o inclusion _ == inclusion _)
              * (projection _ == projection _ $o phi)}.

Proposition equiv_path_abses_data `{Funext} {B A : AbGroup} (E F: AbSES B A)
  : abses_path_data E F <~> abses_path_data_iso E F.
Proof.
  srapply equiv_adjointify.
  - intros [phi [p q]].
    exact ({| grp_iso_homo := phi; isequiv_group_iso := short_five_lemma phi p q |}; (p, q)).
  - srapply (functor_sigma (grp_iso_homo _ _)).
    exact (fun _ => idmap).
  - intros [phi [p q]].
    apply path_sigma_hprop.
    by apply equiv_path_groupisomorphism.
  - reflexivity.
Defined.

Definition equiv_path_abses `{Univalence} {B A : AbGroup} {E F : AbSES B A}
  : abses_path_data E F <~> E = F
  := equiv_path_abses_iso oE equiv_path_abses_data E F.

Definition path_abses `{Univalence} {B A : AbGroup} {E F : AbSES B A} (phi : middle E $-> F)
           (p : phi $o inclusion _ == inclusion _) (q : projection _ == projection _ $o phi)
  : E = F := equiv_path_abses (phi; (p,q)).

(** *** Characterisation of loops of short exact sequences *)

(** Endomorphisms of the trivial short exact sequence in [AbSES B A] correspond to homomorphisms [B -> A]. *)
Lemma abses_endomorphism_trivial `{Funext} {B A : AbGroup}
  : {phi : GroupHomomorphism (point (AbSES B A)) (point (AbSES B A)) &
             (phi o inclusion _ == inclusion _)
             * (projection _ == projection _ o phi)}
      <~> (B $-> A).
Proof.
  srapply equiv_adjointify.
  - intros [phi _].
    exact (ab_biprod_pr1 $o phi $o ab_biprod_inr).
  - intro f.
    snrefine (_;_).
    + refine (ab_biprod_rec ab_biprod_inl _).
      refine (ab_biprod_corec f grp_homo_id).
    + split; intro x; cbn.
      * apply path_prod; cbn.
        -- exact (ap _ (grp_homo_unit f) @ right_identity _).
        -- exact (right_identity _).
      * exact (left_identity _)^.
  - intro f.
    rapply equiv_path_grouphomomorphism; intro b; cbn.
    exact (left_identity _).
  - intros [phi [p q]].
    apply path_sigma_hprop; cbn.
    rapply equiv_path_grouphomomorphism; intros [a b]; cbn.
    apply path_prod; cbn.
    + rewrite (ab_biprod_decompose a b).
      refine (_ @ (grp_homo_op (ab_biprod_pr1 $o phi) _ _)^).
      apply grp_cancelR; symmetry.
      exact (ap fst (p a)).
    + rewrite (ab_biprod_decompose a b).
      refine (_ @ (grp_homo_op (ab_biprod_pr2 $o phi) _ _)^); cbn; symmetry.
      exact (ap011 _ (ap snd (p a)) (q (group_unit, b))^).
Defined.

(** Consequently, the loop space of [AbSES B A] is [GroupHomomorphism B A]. (In fact, [B $-> A] are the loops of any short exact sequence, but the trivial case is easiest to show.) *)
Definition loops_abses `{Univalence} {A B : AbGroup}
  : (B $-> A) <~> loops (AbSES B A)
  := equiv_path_abses oE abses_endomorphism_trivial^-1.

(** We can transfer a loop of the trivial short exact sequence to any other. *)
Definition hom_loops_data_abses `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : (B $-> A) -> abses_path_data E E.
Proof.
  intro phi.
  srefine (_; (_, _)).
  - exact (ab_homo_add grp_homo_id (inclusion E $o phi $o projection E)).
  - intro a; cbn.
    refine (ap (fun x => _ + inclusion E (phi x)) _ @ _).
    1: apply iscomplex_abses.
    refine (ap (fun x => _ + x) (grp_homo_unit (inclusion E $o phi)) @ _).
    apply grp_unit_r.
  - intro e; symmetry.
    refine (grp_homo_op (projection E) _ _ @ _); cbn.
    refine (ap (fun x => _ + x) _ @  _).
    1: apply iscomplex_abses.
    apply grp_unit_r.
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
           {s : B $-> E} (h : projection _ $o s == idmap)
  : (middle E) $-> (@ab_kernel E B (projection _)).
Proof.
  snrapply (grp_kernel_corec (G:=E) (A:=E)).
  - refine (ab_homo_add grp_homo_id (grp_homo_compose ab_homo_negation (s $o (projection _)))).
  - intro x; simpl.
    refine (grp_homo_op (projection _) x _ @ _).
    refine (ap (fun y => (projection _) x + y) _ @ right_inverse ((projection _) x)).
    refine (grp_homo_inv _ _ @ ap (-) _ ).
    apply h.
Defined.

(** The composite [A -> E -> ab_kernel (projection E)] is [grp_cxfib]. *)
Lemma projection_split_to_kernel_beta {B A : AbGroup} (E : AbSES B A)
      {s : B $-> E} (h : (projection _) $o s == idmap)
  : (projection_split_to_kernel E h) $o (inclusion _) == grp_cxfib cx_isexact.
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
            {s : B $-> E} (h : (projection _) $o s == idmap)
  : projection_split_iso E h o (inclusion _) == ab_biprod_inl.
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
  : {s : B $-> E & (projection _) $o s == idmap}
    <-> (E = point (AbSES B A)).
Proof.
  refine (iff_compose _ (iff_equiv equiv_path_abses_iso)); split.
  - intros [s h].
    exists (projection_split_iso E h).
    split.
    + nrapply projection_split_beta.
    + reflexivity.
  - intros [phi [g h]].
    exists (grp_homo_compose (grp_iso_inverse phi) ab_biprod_inr).
    intro x; cbn.
    exact (h _ @ ap snd (eisretr _ _)).
Defined.
