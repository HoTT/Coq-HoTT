From HoTT Require Import Basics Types.
Require Import Truncations.Core.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.FreeGroup.
Require Import Algebra.Groups.GroupCoeq.
Require Import Spaces.Finite Spaces.List.Core.
From HoTT.WildCat Require Import Core Equiv Yoneda.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

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
    (FreeGroup_rec R)
    (FreeGroup_rec (fun x => @group_unit (FreeGroup X)))).
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
      FreeGroup_rec f (gp_relators P r) = group_unit}
    <~> GroupHomomorphism G H.
Proof.
  refine ((equiv_precompose_cat_equiv grp_iso_presentation (z:=H))^-1 oE _).
  refine (equiv_groupcoeq_rec _ _ oE _).
  srefine (equiv_functor_sigma_pb _ oE _).
  2: apply equiv_freegroup_rec.
  apply equiv_functor_sigma_id.
  intros f.
  srapply equiv_iff_hprop.
  { intros p.
    change (equiv_freegroup_rec H _ f $o FreeGroup_rec (gp_relators P)
      $== equiv_freegroup_rec _ _ f $o FreeGroup_rec (fun _ => group_unit)).
    rapply FreeGroup_ind_homotopy.
    exact p. }
  intros p r.
  hnf in p.
  exact (p (freegroup_in r)).
Defined.

(** ** Constructors for finite presentations *)

Definition Build_Finite_GroupPresentation n m
  (f : FinSeq m (FreeGroup (Fin n)))
  : GroupPresentation.
Proof.
  snapply Build_GroupPresentation.
  - exact (Fin n).
  - exact (Fin m).
  - exact f.
Defined.

Instance FinitelyGeneratedPresentation_Build_Finite_GroupPresentation
  {n m f}
  : FinitelyGeneratedPresentation (Build_Finite_GroupPresentation n m f).
Proof.
  unshelve econstructor.
  2: simpl; apply tr; reflexivity.
Defined.

Instance FinitelyRelatedPresentation_Build_Finite_GroupPresentation
  {n m f}
  : FinitelyRelatedPresentation (Build_Finite_GroupPresentation n m f).
Proof.
  unshelve econstructor.
  2: simpl; apply tr; reflexivity.
Defined.

(** ** Notations for presentations *)

(** Convenient abbreviation when defining notations. *)
Local Notation ff := (freegroup_in o fin_nat).

(** TODO: I haven't worked out how to generalize to any number of binders, so we explicitly list the first few levels. *)

Local Open Scope nat_scope.

(** One generator *)
Notation "⟨ x | F , .. , G ⟩" :=
  (Build_Finite_GroupPresentation 1 _
    (fscons ((fun (x : FreeGroup (Fin 1))
      => F : FreeGroup (Fin _)) (ff 0%nat))
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
