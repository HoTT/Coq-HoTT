Require Export Category.Core.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Section category_sum.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition category_sum_morphism (s d : C + D) : Type
    := match (s, d) with
         | (inl s, inl d) => morphism C s d
         | (inr s, inr d) => morphism D s d
         | _ => Empty
       end.

  Global Arguments category_sum_morphism _ _ / .

  Definition category_sum_identity (x : C + D) : category_sum_morphism x x
    := match x with
         | inl x => identity x
         | inr x => identity x
       end.

  Global Arguments category_sum_identity _ / .

  Definition category_sum_compose (s d d' : C + D)
             (m1 : category_sum_morphism d d') (m2 : category_sum_morphism s d)
  : category_sum_morphism s d'.
  Proof.
    case s, d, d'; simpl in *;
    solve [ case m1
          | case m2
          | eapply compose; eassumption ].
  Defined.

  Global Arguments category_sum_compose [_ _ _] _ _ / .

  Definition category_sum : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (C + D)%type
              category_sum_morphism
              category_sum_identity
              category_sum_compose
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
