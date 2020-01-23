(** * Homotopy PreCategory of Types *)
Require Import Category.Core Category.Morphisms.
Require Import HoTT.Basics HoTT.Truncations HSet.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.

Local Open Scope category_scope.

(** Quoting the HoTT Book:

    Example. There is a precategory whose type of objects is [U] and
    with [hom(X,Y) : ∥X → Y∥₀], and composition defined by induction
    on truncation from ordinary composition [(Y → Z) → (X → Y) → (X →
    Z)]. We call this the homotopy precategory of types. *)

(** We don't want access to all of the internals of this category at top level. *)
Module HomotopyPreCategoryInternals.
  Section homotopy_precategory.
    Local Notation object := Type (only parsing).
    Local Notation morphism s d := (Trunc 0 (s -> d)) (only parsing).

    Definition compose s d d' (m : morphism d d') (m' : morphism s d)
    : morphism s d'.
    Proof.
      revert m'; apply Trunc_rec; intro m'.
      revert m; apply Trunc_rec; intro m.
      apply tr.
      exact (m o m')%core.
    Defined.

    Definition identity x : morphism x x
      := tr idmap.

    Global Arguments compose [s d d'] m m' / .
    Global Arguments identity x / .
  End homotopy_precategory.
End HomotopyPreCategoryInternals.

(** ** The Homotopy PreCategory of Types *)
Definition homotopy_precategory : PreCategory.
Proof.
  refine (@Build_PreCategory
            Type
            _
            (@HomotopyPreCategoryInternals.identity)
            (@HomotopyPreCategoryInternals.compose)
            _
            _
            _
            _);
  simpl; intros;
  repeat match goal with
           | [ m : Trunc _ _ |- _ ]
             => revert m;
               apply Trunc_ind;
               [ intro;
                 match goal with
                   | [ |- IsHSet (?a = ?b :> ?T) ]
                     => generalize a b; intros;
                        let H := fresh in
                        assert (H : forall x y : T, IsHProp (x = y))
                 end;
                 typeclasses eauto
               | intro ]
         end;
  simpl;
  apply ap;
  exact idpath.
Defined.
