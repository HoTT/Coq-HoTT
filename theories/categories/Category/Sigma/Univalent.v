(** * Lifting saturation from categories to sigma/subcategories *)
Require Import Category.Core Category.Morphisms.
Require Import Category.Univalent.
Require Import Category.Sigma.Core Category.Sigma.OnObjects Category.Sigma.OnMorphisms.
Require Import HoTT.Types.Sigma HoTT.Basics.Equivalences HoTT.Basics.Trunc HoTT.Basics.PathGroupoids HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation pr1_type := Overture.pr1 (only parsing).

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope equiv_scope.
Local Open Scope function_scope.

(** ** Lift saturation to sigma on objects whenever the property is an hProp *)
Section onobjects.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Global Instance iscategory_sigT_obj `{forall a, IsHProp (Pobj a), A_cat : IsCategory A}
  : IsCategory (sigT_obj A Pobj).
  Proof.
    intros s d.
    refine (isequiv_homotopic
              ((issig_full_isomorphic (sigT_obj A Pobj) _ _ o (issig_full_isomorphic A _ _)^-1)
                 o (@idtoiso A s.1 d.1)
                 o pr1_path)
              _).
    intro x; destruct x.
    reflexivity.
  Defined.

  (** The converse is not true; consider [Pobj := fun _ => Empty]. *)
End onobjects.

(** ** Lift saturation to sigma on objects whenever the property is automatically and uniquely true of isomorphisms *)
Section onmorphisms.
  Variable A : PreCategory.
  Variable Pmor : forall s d, morphism A s d -> Type.

  Local Notation mor s d := { m : _ | Pmor s d m }%type.
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Local Notation A' := (@sigT_mor A Pmor HPmor Pidentity Pcompose P_associativity P_left_identity P_right_identity).

  (** To have any hope of relating [IsCategory A] with [IsCategory
      A'], we assume that [Pmor] is automatically and uniquely true on
      isomorphisms. *)
  Context `{forall s d m, IsIsomorphism m -> Contr (Pmor s d m)}.

  Definition iscategory_sigT_mor_helper {s d}
  : @Isomorphic A' s d -> @Isomorphic A s d.
  Proof.
    refine ((issig_full_isomorphic A _ _) o _ o (issig_full_isomorphic A' _ _)^-1).
    exact (functor_sigma
             pr1_type
             (fun _ =>
                functor_sigma
                  pr1_type
                  (fun _ =>
                     functor_sigma
                       pr1_path
                       (fun _ => pr1_path)))).
  Defined.

  Local Instance isequiv_iscategory_sigT_mor_helper s d
  : IsEquiv (@iscategory_sigT_mor_helper s d).
  Proof.
    refine (isequiv_adjointify _ _ _ _).
    { intro e.
      exists (e : morphism _ _ _; center _).
      exists (e^-1%morphism; center _);
        refine (path_sigma _ _ _ _ _);
        first [ apply left_inverse
              | apply right_inverse
              | by apply path_ishprop ]. }
    { intro; by apply path_isomorphic. }
    { intros x; apply path_isomorphic.
      exact (path_sigma' _ 1 (contr _)). }
  Defined.

  Global Instance iscategory_sigT_mor `{A_cat : IsCategory A}
  : IsCategory A'.
  Proof.
    intros s d.
    refine (isequiv_homotopic
              (iscategory_sigT_mor_helper^-1 o @idtoiso _ _ _)
              _).
    intro x; apply path_isomorphic; cbn.
    destruct x; refine (path_sigma' _ 1 (contr _)).
  Defined.

  Definition iscategory_from_sigT_mor `{A'_cat : IsCategory A'}
  : IsCategory A.
  Proof.
    intros s d.
    refine (isequiv_homotopic
              (iscategory_sigT_mor_helper
                 o (@idtoiso A' _ _))
              _).
    intro x; apply path_isomorphic; cbn.
    destruct x; reflexivity.
  Defined.

  Global Instance isequiv_iscategory_sigT_mor `{Funext}
  : IsEquiv (@iscategory_sigT_mor).
  Proof.
    refine (isequiv_iff_hprop _ (@iscategory_from_sigT_mor)).
  Defined.
End onmorphisms.
