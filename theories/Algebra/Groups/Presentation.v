Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.FreeGroup.
Require Import Algebra.Groups.GroupCoeq.
Require Import Spaces.Finite.
Require Import WildCat.

(** In this file we develop presentations of groups. *)

(** The data of a group presentation *)
Record GroupPresentation := {
  (** We have a type of generators *)
  gp_generators : Type ;
  (** An indexing type for relators *)
  gp_rel_index : Type ;
  (** The relators are picked out amongst elements of the free group on the generators. *)
  gp_relators : gp_rel_index -> FreeGroup gp_generators;
}.

(** Note: A relator is a relation in the form of "w = 1", any relation "w = v" can become a relator "wv^-1 = 1" for words v and w. *)

(** Given the data of a group presentation we can construct the group. This is sometimes called the presented group. *)
Definition group_gp : GroupPresentation -> Group.
Proof.
  intros [X I R].
  exact (GroupCoeq
    (FreeGroup_rec I (FreeGroup X) R)
    (FreeGroup_rec I (FreeGroup X) (fun x => @group_unit (FreeGroup X)))).
Defined.

(** A group [G] has a presentation if there exists a group presentation whose presented group is isomorphic to [G]. *)
Class HasPresentation (G : Group) := {
  presentation : GroupPresentation;
  grp_iso_presentation : GroupIsomorphism (group_gp presentation) G;
}.

Coercion presentation : HasPresentation >-> GroupPresentation.

(** Here are a few finiteness properties of group presentations. *)

(** A group presentation is finitely generated if its generating set is finite. *)
Class FinitelyGeneratedPresentation (P : GroupPresentation)
  := finite_gp_generators : Finite (gp_generators P).

(** A group presentation is finitely related if its relators indexing set is finite. *)
Class FinitelyRelatedPresentation (P : GroupPresentation)
  := finite_gp_relators : Finite (gp_rel_index P).

(** A group presentation is a finite presentation if it is finitely generated and related. *)
Class FinitePresentation (P : GroupPresentation) := {
  fp_generators : FinitelyGeneratedPresentation P;
  fp_relators : FinitelyRelatedPresentation P;
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
Theorem grp_pres_rec {funext : Funext} (G : Group) (P : HasPresentation G) (H : Group)
  : {f : gp_generators P -> H & forall r,
      FreeGroup_rec _ _ f (gp_relators P r) = group_unit}
    <~> GroupHomomorphism G H.
Proof.
  refine ((equiv_precompose_cat_equiv grp_iso_presentation)^-1 oE _).
  refine (equiv_groupcoeq_rec _ _ oE _).
  srefine (equiv_functor_sigma_pb _^-1 oE _).
  2: apply equiv_freegroup_rec.
  apply equiv_functor_sigma_id.
  intros f.
  srapply equiv_iff_hprop.
  { intros p.
    hnf.
    rapply Trunc_ind.
    srapply Coeq.Coeq.Coeq_ind.
    2: intros; apply path_ishprop.
    intros w; hnf.
    induction w.
    1: reflexivity.
    simpl.
    refine (_ @ _ @ _^).
    1,3: exact (grp_homo_op (FreeGroup_rec _ _ _) _ _).
    f_ap.
    destruct a.
    1: refine (p _ @ (grp_homo_unit _)^).
    refine (grp_homo_inv _ _ @ ap _ _ @ (grp_homo_inv _ _)^).
    refine (p _ @ (grp_homo_unit _)^). }
  intros p r.
  hnf in p.
  pose (p' := p o freegroup_eta _).
  clearbody p'; clear p.
  specialize (p' (ListQuotient.word_sing _ (inl r))).
  refine (_ @ p').
  clear p'.
  symmetry.
  refine (grp_homo_op _ _ _ @ _).
  refine (_ @ right_identity _).
  f_ap.
Defined.
