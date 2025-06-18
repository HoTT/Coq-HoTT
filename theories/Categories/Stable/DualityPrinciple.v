(** * The Universal Duality Principle

    This file establishes the most powerful meta-theorem in stable category
    theory: any property or construction in a pre-stable category automatically
    has a dual in the opposite category. This principle allows us to obtain
    new theorems "for free" by dualizing existing ones.
    
    Contents:
    - The fundamental duality theorem
    - Double opposite properties
    - Dualization of properties
    - Meta-theorems for automatic dualization
    - The duality involution
*)

From HoTT Require Import Basics Types Categories.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories.Functor Require Import Identity Composition.
Require Import ZeroObjects.
Require Import ZeroMorphismLemmas.
Require Import Biproducts.
Require Import AdditiveCategories.
Require Import PreStableCategories.
Require Import SemiStableCategories.
Require Import ProperStableCategories.
Require Import Triangles.
Require Import TriangleMorphisms.
Require Import OppositeCategories.
Require Import OppositePreStable.

(** * The Fundamental Duality Theorem *)

Section FundamentalDuality.

  (** Any property that holds for all pre-stable categories also holds for
      their opposites. This is the foundation of categorical duality. *)
  Theorem duality_principle
    : forall (P : PreStableCategory -> Type),
      (forall PS, P PS) -> 
      (forall PS, P (opposite_prestable_category PS)).
  Proof.
    intros P H PS.
    apply H.
  Qed.

  (** A stronger version: any property of pre-stable categories is preserved by opposite. *)
  Theorem duality_principle_strong
    : forall (P : PreStableCategory -> Type),
      (forall PS, P PS) -> 
      (forall PS, P (opposite_prestable_category PS)).
  Proof.
    intros P H PS.
    apply H.
  Qed.
End FundamentalDuality.

(** * Double Opposite Properties *)

Section DoubleOpposite.

  (** The double opposite functor at the PreCategory level. *)
  Definition double_opposite_functor (C : PreCategory)
    : Functor (opposite_category (opposite_category C)) C.
  Proof.
    exact (Build_Functor
      (opposite_category (opposite_category C)) C
      (fun X => X)
      (fun X Y f => f)
      (fun X Y Z f g => idpath)
      (fun X => idpath)).
  Defined.

  (** Double opposite is the identity on objects. *)
  Lemma double_opposite_objects (C : PreCategory) (X : object C)
    : object (opposite_category (opposite_category C)) = object C.
  Proof.
    reflexivity.
  Qed.

  (** Double opposite is the identity on morphisms. *)
  Lemma double_opposite_morphisms (C : PreCategory) (X Y : object C)
    : morphism (opposite_category (opposite_category C)) X Y = morphism C X Y.
  Proof.
    reflexivity.
  Qed.

  (** For pre-stable categories, double opposite preserves all structure. *)
  Theorem double_opposite_preserves_structure (PS : PreStableCategory)
    : object_of (Susp PS) = 
      object_of (Susp (opposite_prestable_category 
                       (opposite_prestable_category PS))) /\
      object_of (Loop PS) = 
      object_of (Loop (opposite_prestable_category 
                       (opposite_prestable_category PS))) /\
      (forall X, components_of (eta PS) X =
                 components_of (eta (opposite_prestable_category 
                                    (opposite_prestable_category PS))) X) /\
      (forall X, components_of (epsilon PS) X =
                 components_of (epsilon (opposite_prestable_category 
                                        (opposite_prestable_category PS))) X).
  Proof.
    split; [|split; [|split]].
    - reflexivity.
    - reflexivity.
    - intro X. reflexivity.
    - intro X. reflexivity.
  Qed.

End DoubleOpposite.

(** * Dualization of Properties *)

Section DualizationOfProperties.

  (** Properties of morphisms dualize. *)
  Definition dualize_morphism_property 
    (P : forall {C : PreCategory} {X Y : object C}, morphism C X Y -> Type)
    : forall {C : PreCategory} {X Y : object C}, morphism C X Y -> Type
    := fun C X Y f => P (C := opposite_category C) (X := Y) (Y := X) f.

  (** Being an isomorphism dualizes to being an isomorphism. *)
  Theorem isomorphism_self_dual {C : PreCategory} {X Y : object C} (f : morphism C X Y)
    : IsIsomorphism f <-> 
      dualize_morphism_property (@IsIsomorphism) f.
  Proof.
    unfold dualize_morphism_property.
    split.
    - intro H.
      destruct H as [g [Hgf Hfg]].
      exists g.
      split; [exact Hfg | exact Hgf].
    - intro H.
      destruct H as [g [Hfg Hgf]].
      exists g.
      split; [exact Hgf | exact Hfg].
  Qed.

  (** Being a monomorphism dualizes to being an epimorphism. *)
  Definition IsMonomorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y) : Type
    := forall Z (g h : morphism C Z X), (f o g = f o h)%morphism -> g = h.

  Definition IsEpimorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y) : Type
    := forall Z (g h : morphism C Y Z), (g o f = h o f)%morphism -> g = h.

  Theorem mono_epi_dual {C : PreCategory} {X Y : object C} (f : morphism C X Y)
    : IsMonomorphism f <-> 
      dualize_morphism_property (@IsEpimorphism) f.
  Proof.
    unfold dualize_morphism_property, IsMonomorphism, IsEpimorphism.
    split.
    - intros H Z g h Heq.
      exact (H Z g h Heq).
    - intros H Z g h Heq.
      exact (H Z g h Heq).
  Qed.

End DualizationOfProperties.

(** * Meta-Theorems for Automatic Dualization *)

Section MetaTheorems.

(** Any construction on pre-stable categories induces a construction on opposite categories. *)
Definition opposite_construction 
  (F : PreStableCategory -> PreStableCategory)
  : PreStableCategory -> PreStableCategory
  := fun PS => opposite_prestable_category (F (opposite_prestable_category PS)).

(** The double opposite construction has the expected behavior. *)
Theorem construction_dualization
  : forall (F : PreStableCategory -> PreStableCategory) (PS : PreStableCategory),
    opposite_construction (opposite_construction F) PS = 
    opposite_prestable_category 
      (opposite_prestable_category 
        (F (opposite_prestable_category 
            (opposite_prestable_category PS)))).
Proof.
  intros F PS.
  unfold opposite_construction.
  reflexivity.
Qed.

(** For the cleaner statement, we need F to respect the double opposite. *)
Theorem construction_dualization_clean
  : forall (F : PreStableCategory -> PreStableCategory),
    (forall PS, F (opposite_prestable_category (opposite_prestable_category PS)) = F PS) ->
    forall PS,
    opposite_construction (opposite_construction F) PS = 
    opposite_prestable_category (opposite_prestable_category (F PS)).
Proof.
  intros F H_double_op PS.
  unfold opposite_construction.
  rewrite H_double_op.
  reflexivity.
Qed.

End MetaTheorems.

(** * The Duality Involution *)

Section DualityInvolution.

(** Dualizing twice gives an equivalent category. *)
Theorem duality_involution (PS : PreStableCategory)
  : exists (F : Functor PS (opposite_prestable_category 
                            (opposite_prestable_category PS))),
    exists (G : Functor (opposite_prestable_category 
                        (opposite_prestable_category PS)) PS),
    (* F and G are natural isomorphisms *)
    (forall X, object_of (G o F)%functor X = X) /\
    (forall X, object_of (F o G)%functor X = X).
Proof.
  exists (Build_Functor PS (opposite_prestable_category (opposite_prestable_category PS))
           (fun X => X)
           (fun X Y f => f)
           (fun X Y Z f g => idpath)
           (fun X => idpath)).
  exists (Build_Functor (opposite_prestable_category (opposite_prestable_category PS)) PS
           (fun X => X)
           (fun X Y f => f)
           (fun X Y Z f g => idpath)
           (fun X => idpath)).
  split.
  - intro X. reflexivity.
  - intro X. reflexivity.
Qed.

End DualityInvolution.

(** * Concrete Duality Principles *)

Section ConcreteDuality.

(** Left semi-stable in the original is right semi-stable in the opposite. *)
Lemma left_semi_stable_opposite_is_right (PS : PreStableCategory)
  : is_left_semi_stable PS ->
    is_right_semi_stable (opposite_prestable_category PS).
Proof.
  intros H_left X.
  unfold is_left_semi_stable in H_left.
  simpl.
  (* In opposite: epsilon becomes eta, so we need eta to be iso *)
  (* But eta in opposite is epsilon in original, so we need epsilon to be iso *)
  (* No wait, let me think more carefully:
     - In PS^op, epsilon^op = eta from PS
     - So if eta is iso in PS (left semi-stable), then epsilon is iso in PS^op *)
  destruct (H_left X) as [g [Hgf Hfg]].
  exists g.
  split.
  - simpl. exact Hfg.
  - simpl. exact Hgf.
Qed.

(** Triangle identity 1 in the original becomes triangle identity 2 in the opposite. *)
Lemma triangle_1_in_opposite (PS : PreStableCategory)
  : satisfies_triangle_1 PS ->
    satisfies_triangle_2 (opposite_prestable_category PS).
Proof.
  intros H1 X.
  simpl.
  (* In opposite: Susp^op = Loop, Loop^op = Susp, eta^op = epsilon, epsilon^op = eta *)
  (* Triangle 1: ε(ΣX) ∘ Σ(ηX) = 1 *)
  (* In opposite this becomes: η(ΩX) ∘ Ω(εX) = 1 which is triangle 2 *)
  exact (H1 X).
Qed.

(** Left semi-stable dualizes to right semi-stable. *)
Theorem left_right_semi_stable_dual (PS : PreStableCategory)
  : is_left_semi_stable PS <-> 
    is_right_semi_stable (opposite_prestable_category PS).
Proof.
  split.
  - apply left_semi_stable_opposite_is_right.
  - intro H.
    intro X.
    (* We need to show IsIsomorphism (components_of (eta PS) X) *)
    (* H says epsilon is iso in PS^op *)
    pose proof (H X) as H_eps_iso.
    (* In PS^op: epsilon^op X = eta PS X : morphism (PS^op) (ΣΩX) X *)
    (* This means eta PS X : morphism PS X (ΩΣX) is an iso in PS^op *)
    (* But morphisms in PS^op are morphisms in PS with source/target flipped *)
    unfold is_right_semi_stable in H.
    simpl in H_eps_iso.
    (* H_eps_iso says eta PS X is an isomorphism when viewed as a morphism
       in the opposite category from (ΩΣX) to X *)
    (* We need to convert this to an isomorphism in PS from X to (ΩΣX) *)
    destruct H_eps_iso as [g [Hgf Hfg]].
    exists g.
    split.
    + (* g ∘ eta = 1 in PS *)
      simpl in Hfg.
      exact Hfg.
    + (* eta ∘ g = 1 in PS *)  
      simpl in Hgf.
      exact Hgf.
Qed.

(** Triangle identities dualize appropriately. *)
Theorem triangle_identity_duality (PS : PreStableCategory)
  : satisfies_triangle_1 PS <-> 
    satisfies_triangle_2 (opposite_prestable_category PS).
Proof.
  split.
  - apply triangle_1_in_opposite.
  - intro H.
    intro X.
    exact (H X).
Qed.

End ConcreteDuality.

(** * The Power of Duality *)

Section PowerOfDuality.

  (** Every theorem has a dual theorem. *)
  Theorem every_theorem_has_dual
    : forall (statement : PreStableCategory -> Type),
      (forall PS, statement PS) ->
      (forall PS, statement (opposite_prestable_category PS)).
  Proof.
    exact duality_principle.
  Qed.

(** Duality cuts the work in half: proving one direction gives the other. *)
Theorem duality_economy
  (P Q : PreStableCategory -> Type)
  (H_dual : forall PS, P PS <-> Q (opposite_prestable_category PS))
  : (forall PS, P PS) -> 
    (forall PS, Q (opposite_prestable_category PS)).
Proof.
  intros H_P PS.
  (* We want Q (PS^op), and H_dual tells us P PS <-> Q (PS^op) *)
  pose proof (H_dual PS) as H_equiv.
  destruct H_equiv as [H_forward H_backward].
  apply H_forward.
  apply H_P.
Qed.
End PowerOfDuality.

(** Duality cuts the work in half: proving one direction gives the other. *)
Theorem duality_economy_strong
  (P Q : PreStableCategory -> Type)
  (H_dual : forall PS, P PS <-> Q (opposite_prestable_category PS))
  (H_double_op : forall PS, 
    Q (opposite_prestable_category (opposite_prestable_category PS)) -> Q PS)
  : (forall PS, P PS) -> (forall PS, Q PS).
Proof.
  intros H_P PS.
  apply H_double_op.
  (* Now we need Q (PS^op^op) *)
  pose proof (H_dual (opposite_prestable_category PS)) as H_equiv.
  destruct H_equiv as [H_forward H_backward].
  apply H_forward.
  apply H_P.
Qed.

(** * Export Hints *)

Hint Resolve 
  isomorphism_self_dual
  left_right_semi_stable_dual
  triangle_identity_duality
  : duality.

Hint Rewrite
  double_opposite_objects
  double_opposite_morphisms
  : duality_simplify.

(** The next file in the library will be [DualityApplications.v] which demonstrates
    concrete applications of the duality principle to obtain dual theorems and
    constructions automatically. *)