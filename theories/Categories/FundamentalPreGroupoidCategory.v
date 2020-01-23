(** * Fundamental Pregroupoids *)
Require Import Category.Core Category.Morphisms.
Require Import HoTT.Truncations PathGroupoids.
Require Import HoTT.Basics HoTT.Types.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.

Local Open Scope category_scope.

(** Quoting the HoTT Book:

    Example. For _any_ type [X], there is a precategory with [X] as
    its type of objects and with [hom(x,y) : ∥x = y∥₀]. The
    composition operation [∥y = z∥₀ → ∥x = y∥₀ → ∥x = z∥₀] is defined
    by induction on truncation from concatenation [(y = z) → (x = y) →
    (x = z)]. We call this the fundamental pregroupoid of [X]. *)

(** We don't want access to all of the internals of a groupoid category at top level. *)
Module FundamentalPreGroupoidCategoryInternals.
  Section fundamental_pregroupoid_category.
    Variable X : Type.

    Local Notation object := X (only parsing).
    Local Notation morphism s d := (Trunc 0 (s = d :> X)) (only parsing).

    Definition compose s d d' (m : morphism d d') (m' : morphism s d)
    : morphism s d'.
    Proof.
      revert m'; apply Trunc_rec; intro m'.
      revert m; apply Trunc_rec; intro m.
      apply tr.
      exact (m' @ m).
    Defined.

    Definition identity x : morphism x x
      := tr (reflexivity _).

    Global Arguments compose [s d d'] m m' / .
    Global Arguments identity x / .
  End fundamental_pregroupoid_category.
End FundamentalPreGroupoidCategoryInternals.

(** ** Categorification of the fundamental pregroupoid of a type *)
Definition fundamental_pregroupoid_category (X : Type) : PreCategory.
Proof.
  refine (@Build_PreCategory
            X
            _
            (@FundamentalPreGroupoidCategoryInternals.identity X)
            (@FundamentalPreGroupoidCategoryInternals.compose X)
            _
            _
            _
            _);
  simpl; intros;
  abstract (
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
      first [ apply concat_p_pp
            | apply concat_1p
            | apply concat_p1 ]
    ).
Defined.
