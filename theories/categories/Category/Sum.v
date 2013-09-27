Require Export Category.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section category_sum.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition morphism_category_sum (s d : C + D) : Type
    := match (s, d) with
         | (inl s, inl d) => morphism C s d
         | (inr s, inr d) => morphism D s d
         | _ => Empty
       end.

  Global Arguments morphism_category_sum _ _ / .

  Definition identity_category_sum (x : C + D) : morphism_category_sum x x
    := match x with
         | inl x => identity x
         | inr x => identity x
       end.

  Global Arguments identity_category_sum _ / .

  Definition compose_category_sum (s d d' : C + D)
             (m1 : morphism_category_sum d d') (m2 : morphism_category_sum s d)
  : morphism_category_sum s d'.
  Proof.
    case s, d, d'; simpl in *;
    solve [ case m1
          | case m2
          | eapply compose; eassumption ].
  Defined.

  Global Arguments compose_category_sum [_ _ _] _ _ / .

  Definition category_sum : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (C + D)%type
              morphism_category_sum
              identity_category_sum
              compose_category_sum
              _
              _
              _
              _);
    abstract (
        repeat (simpl || intros [] || intro);
        auto with morphism;
        typeclasses eauto
      ).
  Defined.
End category_sum.

Infix "+" := category_sum : category_scope.
