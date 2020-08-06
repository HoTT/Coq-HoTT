Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.FreeGroup.
Require Import Algebra.Groups.GroupCoeq.
Require Import Spaces.Finite.

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

(** Note: A relator is a relation in the form of "f(x) = 1", any relation "f(x) = g(x)" can become a relator "f(x)g(x)^-1 = 1". *)

(** Given the data of a group presentation we can construct the group. This is sometimes called the presented group. *)
Definition group_gp : GroupPresentation -> Group.
Proof.
  intros [X I R].
  exact (GroupCoeq
    (FreeGroup_rec I (FreeGroup X) R)
    (FreeGroup_rec I (FreeGroup X) (fun x => mon_unit))).
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

