Require Import Basics Types.
Require Import Truncations.Core.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.FreeGroup.
Require Import Algebra.Groups.GroupCoeq.
Require Import Spaces.Finite Spaces.List.Core.
Require Import WildCat.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** * Presentations of groups *)

(** The data of a group presentation *)
Record GroupPresentation := {
  (** We have a type of generators *)
  gp_generators : Type ;
  (** An indexing type for relators *)
  gp_rel_index : Type ;
  (** The relators are picked out amongst elements of the free group on the generators. *)
  gp_relators : gp_rel_index -> FreeGroup gp_generators;
}.

(** Note: A relator is a relation in the form of [w = 1], any relation [w = v] can become a relator [wv^-1 = 1] for words [v] and [w]. *)

(** ** Category of group presentations *)

(** Group presentations together with their morphisms form a category. We can later show that this category is equivalent to the category of groups. *)

Record GroupPresentationMorphism {p q : GroupPresentation} := {
  gpm_map : gp_generators p $-> FreeGroup (gp_generators q) ;
  gpm_rel_index : gp_rel_index p $-> FreeGroup (gp_rel_index q) ;
  gpm_map_relators
    : FreeGroup_rec gpm_map $o FreeGroup_rec (gp_relators p)
      $== FreeGroup_rec (gp_relators q) $o FreeGroup_rec gpm_rel_index ;
}.
Arguments GroupPresentationMorphism p q : clear implicits.

Definition gpm_idmap (p : GroupPresentation) : GroupPresentationMorphism p p.
Proof.
  snrapply Build_GroupPresentationMorphism.
  - exact freegroup_in.
  - exact freegroup_in.
  - exact ((freegroup_rec_in $@R _) $@ cat_idl _ $@ (cat_idr _)^$
      $@ (_ $@L freegroup_rec_in^$)).
Defined.

Definition gpm_comp {p q r : GroupPresentation}
  (f : GroupPresentationMorphism q r) (g : GroupPresentationMorphism p q)
  : GroupPresentationMorphism p r.
Proof.
  snrapply Build_GroupPresentationMorphism.
  - exact (FreeGroup_rec (gpm_map f) o gpm_map g).
  - exact (FreeGroup_rec (gpm_rel_index f) o gpm_rel_index g).
  - refine (_ $@ vconcat (gpm_map_relators g) (gpm_map_relators f) $@ _^$).
    + snrapply FreeGroup_ind_homotopy; intros x.
      nrapply freegroup_rec_compose.
    + by snrapply FreeGroup_ind_homotopy.
Defined.

Global Instance isgraph_gp : IsGraph GroupPresentation
  := {| Hom := GroupPresentationMorphism |}.

Global Instance is01cat_gp : Is01Cat GroupPresentation
  := {| Id := gpm_idmap; cat_comp := @gpm_comp |}.

Record GroupPresentationHomotopy {p q : GroupPresentation}
  {f g : GroupPresentationMorphism p q} := {
  gph_map_homotopy : gpm_map f $== gpm_map g ;
  gph_rel_index_homotopy : gpm_rel_index f $== gpm_rel_index g ;
}.
Arguments GroupPresentationHomotopy {p q} f g.

Global Instance is2graph_gp : Is2Graph GroupPresentation
  := fun p q => {| Hom := GroupPresentationHomotopy |}.

Definition gph_idmap {p q : GroupPresentation} (f : p $-> q) : f $-> f.
Proof.
  by snrapply Build_GroupPresentationHomotopy.
Defined.

Definition gph_compose {p q : GroupPresentation} {f f' f'' : p $-> q}
  : (f' $-> f'') -> (f $-> f') -> (f $-> f'')
  := fun h1 h2 => {|
  gph_map_homotopy := gph_map_homotopy h1 $o gph_map_homotopy h2;
  gph_rel_index_homotopy := gph_rel_index_homotopy h1 $o gph_rel_index_homotopy h2;
|}.

Global Instance is01cat_gpm {p q : GroupPresentation} : Is01Cat (p $-> q)
  := {| Id := gph_idmap; cat_comp := @gph_compose p q; |}.

Definition gph_inverse {p q : GroupPresentation} {f g : p $-> q}
  : (f $-> g) -> (g $-> f)
  := fun h => {|
  gph_map_homotopy := (gph_map_homotopy h)^$;
  gph_rel_index_homotopy := (gph_rel_index_homotopy h)^$;
|}.

Global Instance is0gpd_gpm {p q : GroupPresentation} : Is0Gpd (p $-> q)
  := {| gpd_rev := @gph_inverse p q |}.

Definition gph_postwhisker {p q r : GroupPresentation}
  (h : q $-> r) {f g : p $-> q} (s : f $== g)
  : h $o f $== h $o g
  := {|
  gph_map_homotopy := _ $@L gph_map_homotopy s;
  gph_rel_index_homotopy := _ $@L gph_rel_index_homotopy s;
|}.

Definition gph_prewhisker {p q r : GroupPresentation}
  (h : p $-> q) {f g : q $-> r} (s : f $== g)
  : f $o h $== g $o h.
Proof.
  snrapply Build_GroupPresentationHomotopy.
  - intros x.
    snrapply FreeGroup_ind_homotopy.
    exact (gph_map_homotopy s).
  - intros x.
    snrapply FreeGroup_ind_homotopy.
    exact (gph_rel_index_homotopy s).
Defined.

Global Instance is1cat_gp : Is1Cat GroupPresentation.
Proof.
  snrapply Build_Is1Cat.
  - exact _.
  - exact _.
  - intros p q r h.
    snrapply Build_Is0Functor.
    exact (@gph_postwhisker p q r h).
  - intros p q r h.
    snrapply Build_Is0Functor.
    exact (@gph_prewhisker p q r h).
  - intros p q r s f g h.
    snrapply Build_GroupPresentationHomotopy.
    1,2: intros x; snrapply freegroup_rec_compose.
  - intros p q r s f g h.
    symmetry.
    snrapply Build_GroupPresentationHomotopy.
    1,2: intros x; snrapply freegroup_rec_compose.
  - intros p q f.
    snrapply Build_GroupPresentationHomotopy.
    1,2: intros x; nrapply freegroup_rec_in.
  - intros p q f.
    snrapply Build_GroupPresentationHomotopy.
    1,2: intros x; nrapply FreeGroup_rec_beta.
Defined.

Global Instance hasequivs_gp : HasEquivs GroupPresentation
  := cat_hasequivs _.

(** ** Group presentations to groups *)

(** Given the data of a group presentation we can construct the group it is meant to be presenting. This is known as the presented group of a group presentation. *)
Definition group_gp : GroupPresentation -> Group
  := fun p => GroupCoeq (FreeGroup_rec (gp_relators p)) zero_morphism.

(** The free group on the generators of a presentation has a natural map to the presented group. *)
Definition group_gp_in_word (p : GroupPresentation)
  : FreeGroup (gp_generators p) $-> group_gp p
  := groupcoeq_in.

Definition group_gp_in (p : GroupPresentation)
  : gp_generators p -> group_gp p
  := group_gp_in_word p o freegroup_in.

(** This map takes relations to the unit element. *)
Definition group_gp_glue' (p : GroupPresentation) (i : gp_rel_index p)
  : group_gp_in_word p (gp_relators p i) = group_gp_in_word _ _
  := groupcoeq_glue (freegroup_in i).

Definition group_gp_glue (p : GroupPresentation) (i : gp_rel_index p)
  : group_gp_in_word p (gp_relators p i) = 1
  := group_gp_glue' p i @ grp_homo_unit _.

Definition group_gp_rec {G : Group} (p : GroupPresentation)
  (f : gp_generators p -> G)
  (h : forall r, FreeGroup_rec f (gp_relators p r) = 1)
  : group_gp p $-> G.
Proof.
  snrapply groupcoeq_rec.
  - exact (FreeGroup_rec f).
  - refine ((freegroup_rec_compose _ _)^$ $@ _).
    nrefine (_ $@ freegroup_const).
    snrapply FreeGroup_ind_homotopy.
    exact h.
Defined.

Definition group_gp_rec_beta_in {G : Group} (p : GroupPresentation)
  (f : gp_generators p -> G)
  (h : forall r, FreeGroup_rec f (gp_relators p r) = 1)
  : group_gp_rec p f h o group_gp_in p == f.
Proof.
  intros x; apply grp_unit_r.
Defined.

Definition group_gp_ind_homotopy {G : Group} {p : GroupPresentation}
  {f g : group_gp p $-> G} (r : f o group_gp_in p == g o group_gp_in p)
  : f $== g.
Proof.
  snrapply groupcoeq_ind_homotopy.
  snrapply FreeGroup_ind_homotopy.
  exact r.
Defined.

Global Instance is0functor_group_gp : Is0Functor group_gp.
Proof.
  snrapply Build_Is0Functor.
  intros p q f.
  snrapply group_gp_rec.
  - exact (group_gp_in_word q o gpm_map f).
  - intros r.
    lhs nrapply freegroup_rec_compose.
    lhs nrapply (ap (group_gp_in_word q) (gpm_map_relators f (freegroup_in r))).
    change ((group_gp_in_word q $o FreeGroup_rec (gp_relators q)) (gpm_rel_index f r)
      = grp_homo_const (gpm_rel_index f r)).
    snrapply FreeGroup_ind_homotopy; clear r; intros r.
    apply group_gp_glue.
Defined.

Definition fmap_group_gp_beta_in {p q : GroupPresentation} (f : p $-> q)
  : fmap group_gp f o group_gp_in p == group_gp_in_word q o gpm_map f.
Proof.
  reflexivity.
Defined.

Definition fmap_group_gp_beta_in_word {p q : GroupPresentation} (f : p $-> q)
  : fmap group_gp f $o group_gp_in_word p
    $== group_gp_in_word q $o FreeGroup_rec (gpm_map f).
Proof.
  by snrapply FreeGroup_ind_homotopy.
Defined.

Global Instance is1functor_group_gp : Is1Functor group_gp.
Proof.
  snrapply Build_Is1Functor.
  - intros p q f g h.
    snrapply group_gp_ind_homotopy.
    intros x; simpl; do 4 f_ap.
    exact (gph_map_homotopy h x).
  - intros p.
    by snrapply group_gp_ind_homotopy.
  - intros p q r f g.
    snrapply group_gp_ind_homotopy.
    intros x.
    rhs nrapply (ap _ (fmap_group_gp_beta_in _ _)).
    rhs nrapply fmap_group_gp_beta_in_word.
    nrapply fmap_group_gp_beta_in.
Defined.

(** ** Standard presentation *)

(** Every group can be given a standard presentation. The set of generators are
  the elements of the groups and the relations are such that the group operation
  agrees with word concatenation. *)
Definition gp_trivial : Group -> GroupPresentation.
Proof.
  intros G.
  snrapply Build_GroupPresentation.
  - exact G.
  - exact (G * G)%type.
  - intros [g h].
    exact ((freegroup_in (g * h))^ * freegroup_in g * freegroup_in h).
Defined.

(** Given a group, we have a homomorphism to the group presented by the standard presentation. *)
Definition group_gp_trivial_corec (G : Group)
  : G $-> group_gp (gp_trivial G).
Proof.
  snrapply (Build_GroupHomomorphism (group_gp_in (gp_trivial G))).
  intros x y.
  unfold group_gp_in.
  rhs_V nrapply grp_homo_op.
  lhs_V nrapply grp_unit_r.
  rewrite <- (group_gp_glue (gp_trivial G) (x, y)).
  lhs_V nrapply grp_homo_op.
  apply ap.
  lhs nrapply grp_assoc.
  snrapply (ap (.* freegroup_in y)).
  rhs_V nrapply grp_unit_l.
  lhs nrapply grp_assoc.
  snrapply (ap (.* freegroup_in x)).
  nrapply grp_inv_r.
Defined.

(** The group presented by the standard presentation is isomorphic to the original group. *)
Definition cate_group_gp_trivial (G : Group)
  : group_gp (gp_trivial G) $<~> G.
Proof.
  snrapply cate_adjointify.
  - snrapply group_gp_rec.
    + exact idmap.
    + simpl.
      intros [g h].
      nrapply grp_inv_l.
  - apply group_gp_trivial_corec.
  - intros x.
    apply grp_unit_r.
  - snrapply group_gp_ind_homotopy.
    intros x.
    simpl.
    apply ap, grp_unit_r.
Defined.

(** In a similar way, every presentation ought to be equivalent to the standard presentation of the presented group. This is far from trivial however. A special case is the Nielson-Schrier theorem for which there are toposes where it fails. *)

(** ** Properties of group presentations *)

(** A group [G] has a presentation if there exists a group presentation whose presented group is isomorphic to [G]. *)
Record HasPresentation (G : Group) := {
  presentation : GroupPresentation;
  grp_iso_presentation : group_gp presentation $<~> G;
}.
Arguments grp_iso_presentation G _ : clear implicits.

Coercion presentation : HasPresentation >-> GroupPresentation.

(** The trivial presentation means that any group has a presentation. *)

Definition haspresentation_trivial (G : Group) : HasPresentation G.
Proof.
  snrapply Build_HasPresentation.
  - exact (gp_trivial G).
  - exact (cate_group_gp_trivial G).
Defined.

(** Here are a few finiteness properties of group presentations. *)

(** A group presentation is finitely generated if its generating set is finite. *)
Class FinitelyGeneratedPresentation (P : GroupPresentation)
  := finite_gp_generators : Finite (gp_generators P).

Global Existing Instance finite_gp_generators.

(** A group presentation is finitely related if its relators indexing set is finite. *)
Class FinitelyRelatedPresentation (P : GroupPresentation)
  := finite_gp_relators : Finite (gp_rel_index P).

Global Existing Instance finite_gp_relators.

(** A group presentation is a finite presentation if it is finitely generated and related. *)
Class FinitePresentation (P : GroupPresentation) := {
  fp_generators :: FinitelyGeneratedPresentation P;
  fp_relators :: FinitelyRelatedPresentation P;
}.

(** These directly translate into properties of groups. *)

(** A group is finitely generated if it has a finitely generated presentation. *)
Class IsFinitelyGenerated (G : Group) := {
  fg_presentation : HasPresentation G;
  fg_presentation_fg : FinitelyGeneratedPresentation fg_presentation;
}.

(** A group is finitely related if it has a finitely related presentation. *)
Class IsFinitelyRelated (G : Group) := {
  fr_presentation : HasPresentation G;
  fr_presentation_fr : FinitelyRelatedPresentation fr_presentation;
}.

Class IsFinitelyPresented (G : Group) := {
  fp_presentation : HasPresentation G;
  fp_presentation_fp : FinitePresentation fp_presentation;
}.

(** ** Fundamental theorem of presentations of groups *)

(** A group homomorphism from a presented group is determined with how the underlying map acts on generators subject to the condition that relators are sent to the unit. *)
Theorem equiv_grp_pres_rec {funext : Funext} (G : Group) (P : HasPresentation G) (H : Group)
  : {f : gp_generators P -> H & forall r,
      FreeGroup_rec f (gp_relators P r) = group_unit}
    <~> GroupHomomorphism G H.
Proof.
  refine ((equiv_precompose_cat_equiv (grp_iso_presentation _ _))^-1 oE _).
  refine (equiv_groupcoeq_rec _ _ oE _).
  srefine (equiv_functor_sigma_pb _ oE _).
  2: apply equiv_freegroup_rec.
  apply equiv_functor_sigma_id.
  intros f.
  srapply equiv_iff_hprop.
  { intros p.
    change (equiv_freegroup_rec H _ f $o FreeGroup_rec (gp_relators P)
      $== equiv_freegroup_rec _ _ f $o grp_homo_const).
    rapply FreeGroup_ind_homotopy.
    exact p. }
  intros p r.
  hnf in p.
  exact (p (freegroup_in r)).
Defined.

(** ** Constructors for finite presentations *)

(** Any finite group is finitely presented via the trivial presentation. *)
Global Instance isfinitelypresented_finite_group {G : Group} {fin : Finite G}
  : IsFinitelyPresented G.
Proof.
  snrapply Build_IsFinitelyPresented.
  - apply haspresentation_trivial.
  - snrapply Build_FinitePresentation; hnf; simpl; exact _.
Defined.

Definition Build_Finite_GroupPresentation n m
  (f : FinSeq m (FreeGroup (Fin n)))
  : GroupPresentation
  := Build_GroupPresentation (Fin n) (Fin m) f.

Global Instance FinitelyGeneratedPresentation_Build_Finite_GroupPresentation
  {n m f}
  : FinitelyGeneratedPresentation (Build_Finite_GroupPresentation n m f)
  := {}.

Global Instance FinitelyRelatedPresentation_Build_Finite_GroupPresentation
  {n m f}
  : FinitelyRelatedPresentation (Build_Finite_GroupPresentation n m f)
  := {}.

(** ** Notations for presentations *)

(** Convenient abbreviation when defining notations. *)
Local Notation ff := (freegroup_in o fin_nat).

(** TODO: I haven't worked out how to generalize to any number of binders, so we explicitly list the first few levels. *)

Local Open Scope nat_scope.

(** One generator *)
Notation "⟨ x | F , .. , G ⟩" :=
  (Build_Finite_GroupPresentation 1 _
    (fscons ((fun (x : FreeGroup (Fin 1))
      => F : FreeGroup (Fin _)) (ff 0))
    .. (fscons ((fun (x : FreeGroup (Fin 1))
      => G : FreeGroup (Fin _)) (ff 0)) fsnil) ..))
  (at level 200, x binder).

(** Two generators *)
Notation "⟨ x , y | F , .. , G ⟩" :=
  (Build_Finite_GroupPresentation 2 _
    (fscons ((fun (x y : FreeGroup (Fin 2))
      => F : FreeGroup (Fin _)) (ff 0) (ff 1))
    .. (fscons ((fun (x y : FreeGroup (Fin 2))
      => G : FreeGroup (Fin _)) (ff 0) (ff 1)) fsnil) ..))
  (at level 200, x binder, y binder).

(** Three generators *)
Notation "⟨ x , y , z | F , .. , G ⟩" :=
  (Build_Finite_GroupPresentation 3 _
    (fscons ((fun (x y z : FreeGroup (Fin 3))
      => F : FreeGroup (Fin _)) (ff 0) (ff 1) (ff 2))
    .. (fscons ((fun (x y z : FreeGroup (Fin 3))
      => G : FreeGroup (Fin _)) (ff 0) (ff 1) (ff 2)) fsnil) ..))
  (at level 200, x binder, y binder, z binder).
