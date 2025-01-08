Require Import Basics Types Truncations.Core.
Require Import HSet WildCat.
Require Import Groups.QuotientGroup Groups.ShortExactSequence.
Require Import AbelianGroup AbGroups.Biproduct AbHom.
Require Import Homotopy.ExactSequence Pointed.
Require Import Modalities.ReflectiveSubuniverse.

Local Open Scope pointed_scope.
Local Open Scope path_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * Short exact sequences of abelian groups *)

(** A short exact sequence of abelian groups consists of a monomorphism [i : A -> E] and an epimorphism [p : E -> B] such that the image of [i] equals the kernel of [p]. Later we will consider short exact sequences up to isomorphism by 0-truncating the type [AbSES] defined below. An isomorphism class of short exact sequences is called an extension. *)

Declare Scope abses_scope.
Local Open Scope abses_scope.

(** The type of short exact sequences [A -> E -> B] of abelian groups. We decorate it with (') to reserve the undecorated name for the structured version. *)
Record AbSES' {B A : AbGroup@{u}} := Build_AbSES {
    middle :  AbGroup@{u};
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
Arguments Build_AbSES {B A}.

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
Global Instance ispointed_abses {B A : AbGroup@{u}}
  : IsPointed (AbSES' B A).
Proof.
  rapply (Build_AbSES (ab_biprod A B) ab_biprod_inl ab_biprod_pr2).
  snrapply Build_IsExact.
  - srapply phomotopy_homotopy_hset; reflexivity.
  - intros [[a b] p]; cbn; cbn in p.
    rapply contr_inhabited_hprop.
    apply tr.
    exists a.
    rapply path_sigma_hprop; cbn.
    exact (path_prod' idpath p^).
Defined.

(** The pointed type of short exact sequences. *)
Definition AbSES (B A : AbGroup@{u}) : pType
  := [AbSES' B A, _].

(** ** Paths in [AbSES B A] *)

Definition abses_path_data_iso
  {B A : AbGroup@{u}} (E F : AbSES B A)
  := {phi : GroupIsomorphism E F
            & (phi $o inclusion _ == inclusion _)
              * (projection _ == projection _ $o phi)}.

(** Having the path data in a slightly different form is useful for [equiv_path_abses_iso]. *)
Local Lemma shuffle_abses_path_data_iso `{Funext}
  {B A : AbGroup@{u}} (E F : AbSES B A)
  : (abses_path_data_iso E F)
      <~> {phi : GroupIsomorphism E F
                 & (phi $o inclusion _ == inclusion _)
                   * (projection _ $o grp_iso_inverse phi
                      == projection _)}.
Proof.
  srapply equiv_functor_sigma_id; intro phi.
  srapply equiv_functor_prod'.
  1: exact equiv_idmap.
  srapply (equiv_functor_forall' phi^-1); intro e; cbn.
  apply equiv_concat_r.
  exact (ap _ (eisretr _ _)).
Defined.

(** Paths in [AbSES] correspond to isomorphisms between the [middle]s respecting [inclusion] and [projection]. Below we prove the stronger statement [equiv_path_abses], which uses this result. *)
Proposition equiv_path_abses_iso `{Univalence}
  {B A : AbGroup@{u}} {E F : AbSES' B A}
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
Global Instance istrunc_abses `{Univalence} {B A : AbGroup@{u}}
  : IsTrunc 1 (AbSES B A).
Proof.
  apply istrunc_S.
  intros E F.
  refine (istrunc_equiv_istrunc _ equiv_path_abses_iso (n:=0)).
  rapply istrunc_sigma.
  apply ishset_groupisomorphism.
Defined.

Definition path_abses_iso `{Univalence} {B A : AbGroup@{u}}
  {E F : AbSES B A}
  (phi : GroupIsomorphism E F) (p : phi $o inclusion _ == inclusion _)
  (q : projection _ == projection _ $o phi)
  : E = F := equiv_path_abses_iso (phi; (p,q)).

(** Given [p] and [q], the map [phi] just above is automatically an isomorphism. Showing this requires the "short five lemma." *)

(** A special case of the "short 5-lemma" where the two outer maps are (definitionally) identities. *)
Lemma short_five_lemma {B A : AbGroup@{u}}
  {E F : AbSES B A} (phi : GroupHomomorphism E F)
  (p0 : phi $o inclusion E == inclusion F) (p1 : projection E == projection F $o phi)
  : IsEquiv phi.
Proof.
  apply isequiv_surj_emb.
  - intro f.
    rapply contr_inhabited_hprop.
    (** Since [projection E] is epi, we can pull [projection F f] back to [e0 : E].*)
    assert (e0 : Tr (-1) (hfiber (projection E) (projection F f))).
    1: apply center, issurjection_projection.
    strip_truncations.
    (** The difference [f - (phi e0.1)] is sent to [0] by [projection F], hence lies in [A]. *)
    assert (a : Tr (-1) (hfiber (inclusion F) (f - phi e0.1))).
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
  - apply isembedding_istrivial_kernel.
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
Definition abses_path_data {B A : AbGroup@{u}} (E F : AbSES B A)
  := {phi : GroupHomomorphism E F
            & (phi $o inclusion _ == inclusion _)
              * (projection _ == projection _ $o phi)}.

Definition abses_path_data_to_iso {B A : AbGroup@{u}} (E F: AbSES B A)
  : abses_path_data E F -> abses_path_data_iso E F.
Proof.
  - intros [phi [p q]].
    exact ({| grp_iso_homo := phi; isequiv_group_iso := short_five_lemma phi p q |}; (p, q)).
Defined.

Proposition equiv_path_abses_data `{Funext} {B A : AbGroup@{u}} (E F: AbSES B A)
  : abses_path_data E F <~> abses_path_data_iso E F.
Proof.
  srapply equiv_adjointify.
  - apply abses_path_data_to_iso.
  - srapply (functor_sigma (grp_iso_homo _ _)).
    exact (fun _ => idmap).
  - intros [phi [p q]].
    apply path_sigma_hprop.
    by apply equiv_path_groupisomorphism.
  - reflexivity.
Defined.

Definition equiv_path_abses `{Univalence} {B A : AbGroup@{u}} {E F : AbSES B A}
  : abses_path_data E F <~> E = F
  := equiv_path_abses_iso oE equiv_path_abses_data E F.

Definition path_abses `{Univalence} {B A : AbGroup@{u}}
  {E F : AbSES B A} (phi : middle E $-> F)
  (p : phi $o inclusion _ == inclusion _) (q : projection _ == projection _ $o phi)
  : E = F := equiv_path_abses (phi; (p,q)).

(** *** The wildcat of short exact sequences *)

Global Instance isgraph_abses_path_data {A B : AbGroup@{u}} (E F : AbSES B A)
  : IsGraph (abses_path_data_iso E F)
  := isgraph_induced (grp_iso_homo _ _ o pr1).

Global Instance is01cat_abses_path_data {A B : AbGroup@{u}} (E F : AbSES B A)
  : Is01Cat (abses_path_data_iso E F)
  := is01cat_induced (grp_iso_homo _ _ o pr1).

Global Instance is0gpd_abses_path_data {A B : AbGroup@{u}} (E F : AbSES B A)
  : Is0Gpd (abses_path_data_iso E F)
  := is0gpd_induced (grp_iso_homo _ _ o pr1).

Global Instance isgraph_abses {A B : AbGroup@{u}} : IsGraph (AbSES B A)
  := Build_IsGraph _ abses_path_data_iso.

(** The path data corresponding to [idpath]. *)
Definition abses_path_data_1 {B A : AbGroup@{u}} (E : AbSES B A)
  : E $-> E := (grp_iso_id; (fun _ => idpath, fun _ => idpath)).

(** We can compose path data in [AbSES B A]. *)
Definition abses_path_data_compose {B A : AbGroup@{u}} {E F G : AbSES B A}
           (p : E $-> F) (q : F $-> G) : E $-> G
  := (q.1 $oE p.1; ((fun x => ap q.1 (fst p.2 x) @ fst q.2 x),
                     (fun x => snd p.2 x @ snd q.2 (p.1 x)))).

Global Instance is01cat_abses {A B : AbGroup@{u}}
  : Is01Cat (AbSES B A)
  := Build_Is01Cat _ _ abses_path_data_1
       (fun _ _ _ q p => abses_path_data_compose p q).

Definition abses_path_data_inverse
  {B A : AbGroup@{u}} {E F : AbSES B A}
  : (E $-> F) -> (F $-> E).
Proof.
  intros [phi [p q]].
  srefine (_; (_,_)).
  - exact (grp_iso_inverse phi).
  - intro a.
    exact (ap _ (p a)^ @ eissect _ (inclusion E a)).
  - intro a; simpl.
    exact (ap (projection F) (eisretr _ _)^ @ (q _)^).
Defined.

Global Instance is0gpd_abses
  {A B : AbGroup@{u}} : Is0Gpd (AbSES B A)
  := {| gpd_rev := fun _ _ => abses_path_data_inverse |}.

Global Instance is2graph_abses
  {A B : AbGroup@{u}} : Is2Graph (AbSES B A)
  := fun E F => isgraph_abses_path_data E F.

(** [AbSES B A] forms a 1Cat *)
Global Instance is1cat_abses {A B : AbGroup@{u}}
  : Is1Cat (AbSES B A).
Proof.
  snrapply Build_Is1Cat'.
  1: intros ? ?; apply is01cat_abses_path_data.
  1: intros ? ?; apply is0gpd_abses_path_data.
  3-5: cbn; reflexivity.
  1,2: intros E F G f;
  srapply Build_Is0Functor;
  intros p q h e; cbn.
  - exact (ap f.1 (h e)).
  - exact (h (f.1 e)).
Defined.

Global Instance is1gpd_abses {A B : AbGroup@{u}}
  : Is1Gpd (AbSES B A).
Proof.
  rapply Build_Is1Gpd;
    intros E F p e; cbn.
  - apply eissect.
  - apply eisretr.
Defined.

Global Instance hasmorext_abses `{Funext} {A B : AbGroup@{u}}
  : HasMorExt (AbSES B A).
Proof.
  srapply Build_HasMorExt;
    intros E F f g.
  srapply isequiv_homotopic'; cbn.
  1: exact (((equiv_path_groupisomorphism _ _)^-1%equiv)
              oE (equiv_path_sigma_hprop _ _)^-1%equiv).
  intro p; by induction p.
Defined.

(** *** Path data lemmas *)

(** We need to be able to work with path data as if they're paths. Our preference is to state things in terms of [abses_path_data_iso], since this lets us keep track of isomorphisms whose inverses compute. The "abstract" inverses produced by [short_five_lemma] do not compute well. *)

Definition equiv_path_abses_1 `{Univalence} {B A : AbGroup@{u}} {E : AbSES B A}
  : equiv_path_abses_iso (abses_path_data_1 E) = idpath.
Proof.
  apply (equiv_ap_inv' equiv_path_abses_iso).
  refine (eissect _ _ @ _).
  srapply path_sigma_hprop; simpl.
  srapply equiv_path_groupisomorphism.
  reflexivity.
Defined.

Definition equiv_path_absesV_1 `{Univalence} {B A : AbGroup@{u}} {E : AbSES B A}
  : (@equiv_path_abses_iso _ B A E E)^-1 idpath = Id E.
Proof.
  apply moveR_equiv_M; symmetry.
  apply equiv_path_abses_1.
Defined.

Definition abses_path_data_V `{Univalence} {B A : AbGroup@{u}} {E F : AbSES B A}
           (p : abses_path_data_iso E F)
  : (equiv_path_abses_iso p)^ = equiv_path_abses_iso (abses_path_data_inverse p).
Proof.
  revert p.
  equiv_intro (equiv_path_abses_iso (E:=E) (F:=F))^-1 p; induction p.
  refine (ap _ (eisretr _ _) @ _); symmetry.
  nrefine (ap (equiv_path_abses_iso o abses_path_data_inverse) equiv_path_absesV_1 @ _).
  refine (ap equiv_path_abses_iso gpd_strong_rev_1 @ _).
  exact equiv_path_abses_1.
Defined.

(** Composition of path data corresponds to composition of paths. *)
Definition abses_path_compose_beta `{Univalence} {B A : AbGroup@{u}} {E F G : AbSES B A}
          (p : E = F) (q : F = G)
 : p @ q = equiv_path_abses_iso
             (abses_path_data_compose
                (equiv_path_abses_iso^-1 p) (equiv_path_abses_iso^-1 q)).
Proof.
  induction p, q.
  refine (equiv_path_abses_1^ @ _).
  apply (ap equiv_path_abses_iso).
  apply path_sigma_hprop.
  by apply equiv_path_groupisomorphism.
Defined.

(** A second beta-principle where you start with path data instead of actual paths. *)
Definition abses_path_data_compose_beta `{Univalence} {B A : AbGroup@{u}} {E F G : AbSES B A}
           (p : abses_path_data_iso E F) (q : abses_path_data_iso F G)
  : equiv_path_abses_iso p @ equiv_path_abses_iso q
    = equiv_path_abses_iso (abses_path_data_compose p q).
Proof.
  generalize p, q.
  equiv_intro ((equiv_path_abses_iso (E:=E) (F:=F))^-1) x.
  equiv_intro ((equiv_path_abses_iso (E:=F) (F:=G))^-1) y.
  refine ((eisretr _ _ @@ eisretr _ _) @ _).
  rapply abses_path_compose_beta.
Defined.

(** *** Homotopies of path data *)

Definition equiv_path_data_homotopy `{Univalence} {X : Type} {B A : AbGroup@{u}}
           (f g : X -> AbSES B A) : (f $=> g) <~> f == g.
Proof.
  srapply equiv_functor_forall_id; intro x; cbn.
  srapply equiv_path_abses_iso.
Defined.

Definition pmap_abses_const {B' A' B A : AbGroup@{u}} : AbSES B A -->* AbSES B' A'
  := Build_BasepointPreservingFunctor (const pt) (Id pt).

Definition to_pointed `{Univalence} {B' A' B A : AbGroup@{u}}
  : (AbSES B A -->* AbSES B' A') -> (AbSES B A ->* AbSES B' A')
  := fun f => Build_pMap _ _ f (equiv_path_abses_iso (bp_pointed f)).

Lemma pmap_abses_const_to_pointed `{Univalence} {B' A' B A : AbGroup@{u}}
  : pconst ==* to_pointed (@pmap_abses_const B' A' B A).
Proof.
  srapply Build_pHomotopy.
  1: reflexivity.
  apply moveL_pV.
  refine (concat_1p _ @ _).
  apply equiv_path_abses_1.
Defined.

Lemma abses_ap_fmap `{Univalence} {B0 B1 A0 A1 : AbGroup@{u}}
      (f : AbSES B0 A0 -> AbSES B1 A1) `{!Is0Functor f, !Is1Functor f}
      {E F : AbSES B0 A0} (p : E $== F)
  : ap f (equiv_path_abses_iso p) = equiv_path_abses_iso (fmap f p).
Proof.
  revert p.
  apply (equiv_ind equiv_path_abses_iso^-1%equiv);
    intro p.
  induction p.
  refine (ap (ap f) (eisretr _ _) @ _).
  nrefine (_ @ ap equiv_path_abses_iso _).
  2: { rapply path_hom.
       srefine (_ $@ fmap2 _ _).
       2: exact (Id E).
       2: intro x; reflexivity.
       exact (fmap_id f _)^$. }
  exact equiv_path_abses_1^.
Defined.

Definition to_pointed_compose `{Univalence} {B0 B1 B2 A0 A1 A2 : AbGroup@{u}}
           (f : AbSES B0 A0 -->* AbSES B1 A1) (g : AbSES B1 A1 -->* AbSES B2 A2)
           `{!Is1Functor f, !Is1Functor g}
  : to_pointed g o* to_pointed f ==* to_pointed (g $o* f).
Proof.
  srapply Build_pHomotopy.
  1: reflexivity.
  lazy beta.
  nrapply moveL_pV.
  nrefine (concat_1p _ @ _).
  unfold pmap_compose, Build_pMap, pointed_fun, point_eq, dpoint_eq.
  refine (_ @ ap (fun x => x @ _) _^).
  2: apply (abses_ap_fmap g).
  nrefine (_ @ (abses_path_data_compose_beta _ _)^).
  nrapply (ap equiv_path_abses_iso).
  rapply path_hom.
  reflexivity.
Defined.

Definition equiv_ptransformation_phomotopy `{Univalence} {B' A' B A : AbGroup@{u}}
           {f g : AbSES B A -->* AbSES B' A'}
  : f $=>* g <~> to_pointed f ==* to_pointed g.
Proof.
  refine (issig_pforall _ _ oE _).
  apply (equiv_functor_sigma' (equiv_path_data_homotopy f g)); intro h.
  refine (equiv_concat_r _ _ oE _).
  1: exact ((abses_path_data_compose_beta _ _)^ @ ap (fun x => _ @ x) (abses_path_data_V _)^).
  refine (equiv_ap' equiv_path_abses_iso _ _ oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_groupisomorphism.
Defined.

(** *** Characterisation of loops of short exact sequences *)

(** Endomorphisms of the trivial short exact sequence in [AbSES B A] correspond to homomorphisms [B -> A]. *)
Lemma abses_endomorphism_trivial `{Funext} {B A : AbGroup@{u}}
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
    + rewrite (grp_prod_decompose a b).
      refine (_ @ (grp_homo_op (ab_biprod_pr1 $o phi) _ _)^).
      apply grp_cancelR; symmetry.
      exact (ap fst (p a)).
    + rewrite (grp_prod_decompose a b).
      refine (_ @ (grp_homo_op (ab_biprod_pr2 $o phi) _ _)^); cbn; symmetry.
      exact (ap011 _ (ap snd (p a)) (q (group_unit, b))^).
Defined.

(** Consequently, the loop space of [AbSES B A] is [GroupHomomorphism B A]. (In fact, [B $-> A] are the loops of any short exact sequence, but the trivial case is easiest to show.) *)
Definition loops_abses `{Univalence} {A B : AbGroup}
  : (B $-> A) <~> loops (AbSES B A)
  := equiv_path_abses oE abses_endomorphism_trivial^-1.

(** We can transfer a loop of the trivial short exact sequence to any other. *)
Definition hom_loops_data_abses {A B : AbGroup} (E : AbSES B A)
  : (B $-> A) -> abses_path_data E E.
Proof.
  intro phi.
  srefine (_; (_, _)).
  - exact (grp_homo_id + (inclusion E $o phi $o projection E)).
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
Record AbSESMorphism {A X B Y : AbGroup@{u}}
  {E : AbSES B A} {F : AbSES Y X} := {
    component1 : A $-> X;
    component2 : middle E $-> middle F;
    component3 : B $-> Y;
    left_square : (inclusion _) $o component1 == component2 $o (inclusion _);
    right_square : (projection _) $o component2 == component3 $o (projection _);
  }.

Arguments AbSESMorphism {A X B Y} E F.
Arguments Build_AbSESMorphism {_ _ _ _ _ _} _ _ _ _ _.

Definition issig_AbSESMorphism {A X B Y : AbGroup@{u}}
           {E : AbSES B A} {F : AbSES Y X}
  : { f : (A $-> X) * (middle E $-> middle F) * (B $-> Y)
          & ((inclusion _) $o (fst (fst f)) == (snd (fst f)) $o (inclusion _))
            * ((projection F) $o (snd (fst f)) == (snd f) $o (projection _)) }
      <~> AbSESMorphism E F := ltac:(make_equiv).

(** The identity morphism from [E] to [E]. *)
Lemma abses_morphism_id {A B : AbGroup@{u}} (E : AbSES B A)
  : AbSESMorphism E E.
Proof.
  snrapply (Build_AbSESMorphism grp_homo_id grp_homo_id grp_homo_id).
  1,2: reflexivity.
Defined.

Definition absesmorphism_compose {A0 A1 A2 B0 B1 B2 : AbGroup@{u}}
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
  - refine (grp_homo_id - (s $o projection _)).
  - intro x; simpl.
    refine (grp_homo_op (projection _) x _ @ _).
    refine (ap (fun y => (projection _) x + y) _ @ right_inverse ((projection _) x)).
    refine (grp_homo_inv _ _ @ ap (-) _).
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
  exact (ap _ (grp_homo_unit _) @ grp_inv_unit).
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
        apply (ap negate).
        apply (ap s).
        refine (grp_homo_op (projection _) a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
      * refine (grp_homo_op (projection _) a.1 (s b) @ _).
        exact (ap (fun y => y + _) a.2 @ left_identity _ @ h b).
    + intro e; simpl.
      by apply grp_moveR_gM.
Defined.

(** The full isomorphism [E -> A + B]. *)
Definition projection_split_iso {B A : AbGroup@{u}}
  (E : AbSES B A) {s : GroupHomomorphism B E}
  (h : (projection _) $o s == idmap)
  : GroupIsomorphism E (ab_biprod A B).
Proof.
  etransitivity (ab_biprod (ab_kernel _) B).
  - exact (projection_split_iso1 E h).
  - srapply (equiv_functor_ab_biprod
               (grp_iso_inverse _) grp_iso_id).
    rapply grp_iso_cxfib.
Defined.

Proposition projection_split_beta {B A : AbGroup} (E : AbSES B A)
            {s : B $-> E} (h : (projection _) $o s == idmap)
  : projection_split_iso E h o (inclusion _) == ab_biprod_inl.
Proof.
  intro a.
  (* The next two lines might help the reader, but both are definitional equalities:
  lhs nrapply (ap _ (grp_prod_corec_natural _ _ _ _)).
  lhs nrapply ab_biprod_functor_beta.
  *)
  nrapply path_prod'.
  2: rapply cx_isexact.
  (* The LHS of the remaining goal is definitionally equal to
       (grp_iso_inverse (grp_iso_cxfib (isexact_inclusion_projection E)) $o
         (projection_split_to_kernel E h $o inclusion E)) a
     allowing us to do: *)
  lhs nrapply (ap _ (projection_split_to_kernel_beta E h a)).
  apply eissect.
Defined.

(** A short exact sequence [E] in [AbSES B A] is trivial if and only if [projection E] splits. *)
Proposition iff_abses_trivial_split `{Univalence}
  {B A : AbGroup@{u}} (E : AbSES B A)
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

(** ** Constructions of short exact sequences *)

(** Any inclusion [i : A $-> E] determines a short exact sequence by quotienting. *)
Definition abses_from_inclusion `{Univalence}
  {A E : AbGroup@{u}} (i : A $-> E) `{IsEmbedding i}
  : AbSES (QuotientAbGroup E (grp_image_embedding i)) A.
Proof.
  srapply (Build_AbSES E i).
  1: exact grp_quotient_map.
  1: exact _.
  srapply Build_IsExact.
  - srapply phomotopy_homotopy_hset.
    intro x.
    apply qglue; cbn.
    exists (-x).
    exact (grp_homo_inv _ _ @ (grp_unit_r _)^).
  - snrapply (conn_map_homotopic (Tr (-1)) (B:=grp_kernel (@grp_quotient_map E _))).
    + exact (grp_kernel_quotient_iso _ o ab_image_in_embedding i).
    + intro a.
      by rapply (isinj_embedding (subgroup_incl _)).
    + rapply conn_map_isequiv.
Defined.

(** Conversely, given a short exact sequence [A -> E -> B], [A] is the kernel of [E -> B]. (We don't need exactness at [B], so we drop this assumption.) *)
Lemma abses_kernel_iso `{Funext} {A E B : AbGroup} (i : A $-> E) (p : E $-> B)
  `{IsEmbedding i, IsExact (Tr (-1)) _ _ _ i p}
  : GroupIsomorphism A (ab_kernel p).
Proof.
  snrapply Build_GroupIsomorphism.
  - apply (grp_kernel_corec i).
    rapply cx_isexact.
  - apply isequiv_surj_emb.
    2: rapply (cancelL_mapinO _ (grp_kernel_corec _ _) _).
    intros [y q].
    assert (a : Tr (-1) (hfiber i y)).
    1: by rapply isexact_preimage.
    strip_truncations; destruct a as [a r].
    rapply contr_inhabited_hprop.
    refine (tr (a; _)); cbn.
    apply path_sigma_hprop; cbn.
    exact r.
Defined.

(** A computation rule for the inverse of [abses_kernel_iso i p]. *)
Lemma abses_kernel_iso_inv_beta `{Funext} {A E B : AbGroup} (i : A $-> E) (p : E $-> B)
  `{IsEmbedding i, IsExact (Tr (-1)) _ _ _ i p}
  : i o (abses_kernel_iso i p)^-1 == subgroup_incl _.
Proof.
  rapply (equiv_ind (abses_kernel_iso i p)); intro a.
  exact (ap i (eissect (abses_kernel_iso i p) _)).
Defined.

(* Any surjection [p : E $-> B] induces a short exact sequence by taking the kernel. *)
Lemma abses_from_surjection {E B : AbGroup@{u}} (p : E $-> B) `{IsSurjection p}
  : AbSES B (ab_kernel p).
Proof.
  srapply (Build_AbSES E _ p).
  1: exact (subgroup_incl _).
  1: exact _.
  snrapply Build_IsExact.
  - apply phomotopy_homotopy_hset.
    intros [e q]; cbn.
    exact q.
  - rapply conn_map_isequiv.
Defined.

(** Conversely, given a short exact sequence [A -> E -> B], [B] is the cokernel of [A -> E]. In fact, we don't need exactness at [A], so we drop this from the statement. *)
Lemma abses_cokernel_iso `{Funext}
  {A E B : AbGroup@{u}} (f : A $-> E) (g : GroupHomomorphism E B)
  `{IsSurjection g, IsExact (Tr (-1)) _ _ _ f g}
  : GroupIsomorphism (ab_cokernel f) B.
Proof.
  snrapply Build_GroupIsomorphism.
  - snrapply (quotient_abgroup_rec _ _ g).
    intros e; rapply Trunc_rec; intros [a p].
    refine (ap _ p^ @ _).
    rapply cx_isexact.
  - apply isequiv_surj_emb.
    1: rapply cancelR_conn_map.
    apply isembedding_isinj_hset.
    srapply Quotient_ind2_hprop; intros x y.
    intro p.
    apply qglue; cbn.
    refine (isexact_preimage (Tr (-1)) _ _ (-x + y) _).
    refine (grp_homo_op _ _ _ @ _).
    rewrite grp_homo_inv.
    apply grp_moveL_M1^-1.
    exact p^.
Defined.

Definition abses_cokernel_iso_inv_beta `{Funext}
  {A E B : AbGroup} (f : A $-> E) (g : GroupHomomorphism E B)
  `{IsSurjection g, IsExact (Tr (-1)) _ _ _ f g}
  : (abses_cokernel_iso f g)^-1 o g == grp_quotient_map.
Proof.
  intro x; by apply moveR_equiv_V.
Defined.
