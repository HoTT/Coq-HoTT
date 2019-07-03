(** * Coercions between the various (co)unit definitions *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Adjoint.UnitCounit Adjoint.Dual.
Require Import Functor.Composition.Core Functor.Identity NaturalTransformation.Composition.Core.
Require Import HoTT.Tactics Basics.Trunc Types.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope category_scope.
Local Open Scope morphism_scope.

Section equivalences.
  Section from_unit_counit.
    Local Ltac unit_counit_of_t :=
      repeat
        match goal with
          | _ => split
          | _ => intro
          | _ => progress auto with morphism
          | _ => progress simpl
          | _ => rewrite !composition_of
          | [ |- context[components_of ?T] ]
            => (try_associativity_quick simpl rewrite <- (commutes T));
              try_associativity_quick
                progress
                rewrite ?unit_counit_equation_1, ?unit_counit_equation_2
          | [ |- context[components_of ?T] ]
            => (try_associativity_quick simpl rewrite (commutes T));
              try_associativity_quick
                progress
                rewrite ?unit_counit_equation_1, ?unit_counit_equation_2
          | _ => progress path_induction
        end.

    (** ** unit+counit+zig+zag → unit+UMP *)
    Definition adjunction_unit__of__adjunction_unit_counit
               C D F G (A : @AdjunctionUnitCounit C D F G)
    : AdjunctionUnit F G.
    Proof.
      exists (unit A).
      intros c d f.
      apply contr_inhabited_hprop;
        [ apply hprop_allpath
        | (exists (counit A d o F _1 f));
          abstract unit_counit_of_t ].
      intros [? ?] [? ?].
      apply path_sigma_uncurried.
      let A := match goal with |- @sigT ?A ?P => constr:(A) end in
      let H := fresh in
      assert (H : A);
        [
        | exists H;
            exact (center _) ].
      simpl.
      let x := match goal with |- ?x = ?y => constr:(x) end in
      let y := match goal with |- ?x = ?y => constr:(y) end in
      rewrite <- (right_identity _ _ _ x),
      <- (right_identity _ _ _ y),
      <- !(unit_counit_equation_1 A),
      <- ?associativity;
        repeat simpl rewrite <- (commutes (counit A));
        (try_associativity_quick rewrite <- !composition_of);
        repeat apply ap;
        etransitivity; [ | symmetry ]; eassumption.
    Defined.

    (** ** unit+counit+zig+zag → counit+UMP *)
    Definition adjunction_counit__of__adjunction_unit_counit
               C D F G (A : @AdjunctionUnitCounit C D F G)
    : AdjunctionCounit F G
      := adjunction_counit__op__adjunction_unit
           (adjunction_unit__of__adjunction_unit_counit A^op).
  End from_unit_counit.

  Section to_unit_counit.
    Ltac to_unit_counit_nt helper commutes_tac :=
      simpl;
      intros;
      apply helper;
      repeat match goal with
               | _ => reflexivity
               | _ => rewrite !composition_of
               | _ => progress
                        rewrite ?identity_of, ?left_identity, ?right_identity
               | [ |- context[?x.1] ]
                 => try_associativity_quick simpl rewrite x.2
               | [ |- context[components_of ?T] ]
                 => simpl_do_clear commutes_tac (commutes T)
             end.

    (** ** unit+UMP → unit+counit+zig+zag *)
    Section from_unit.
      Variables C D : PreCategory.
      Variable F : Functor C D.
      Variable G : Functor D C.

      Lemma counit_natural_transformation__of__adjunction_unit_helper
            (A : AdjunctionUnit F G)
            s d (m : morphism D s d)
            (eta := A.1)
            (eps := fun X => (@center _ (A.2 (G X) X 1)).1)
      : G _1 (eps d o F _1 (G _1 m)) o eta (G s) = G _1 m
        -> G _1 (m o eps s) o eta (G s) = G _1 m
        -> eps d o F _1 (G _1 m) = m o eps s.
      Proof.
        intros.
        transitivity (@center _ (A.2 _ _ (G _1 m))).1; [ symmetry | ];
        let x := match goal with |- _ = ?x => constr:(x) end in
        refine ((fun H => ap pr1 (@contr _ (A.2 _ _ (G _1 m)) (x; H))) _);
        assumption.
      Qed.

      Definition counit_natural_transformation__of__adjunction_unit
                 (A : AdjunctionUnit F G)
      : NaturalTransformation (F o G) 1.
      Proof.
        refine (Build_NaturalTransformation
                  (F o G) 1
                  (fun d => (@center _ (A.2 (G d) d 1)).1)
                  _).
        abstract (
            to_unit_counit_nt
              counit_natural_transformation__of__adjunction_unit_helper
              ltac:(fun H => try_associativity_quick rewrite <- H)
          ).
      Defined.

      Definition zig__of__adjunction_unit
                 (A : AdjunctionUnit F G)
                 (Y : C)
                 (eta := A.1)
                 (eps := fun X => (@center _ (A.2 (G X) X 1)).1)
      : G _1 (eps (F Y) o F _1 (eta Y)) o eta Y = eta Y
        -> eps (F Y) o F _1 (eta Y) = 1.
      Proof.
        intros.
        etransitivity; [ symmetry | ];
        simpl_do_clear
          ltac:(fun H => apply H)
                 (fun y H => (@contr _ (A.2 _ _ (A.1 Y)) (y; H))..1);
        try assumption.
        simpl.
        rewrite ?identity_of, ?left_identity, ?right_identity;
          reflexivity.
      Qed.

      Definition adjunction_unit_counit__of__adjunction_unit
                 (A : AdjunctionUnit F G)
      : AdjunctionUnitCounit F G.
      Proof.
        exists A.1
               (counit_natural_transformation__of__adjunction_unit A);
        simpl;
        intros;
        try match goal with
              | [ |- context[?x.1] ] => exact x.2
            end;
        [].
        abstract (to_unit_counit_nt
                    zig__of__adjunction_unit
                    ltac:(fun H => try_associativity_quick rewrite <- H)).
      Defined.
    End from_unit.

    (** ** counit+UMP → unit+counit+zig+zag *)
    Definition adjunction_unit_counit__of__adjunction_counit
               C D F G (A : @AdjunctionCounit C D F G)
    : AdjunctionUnitCounit F G
      := ((adjunction_unit_counit__of__adjunction_unit
             (adjunction_unit__op__adjunction_counit__inv A))^op)%adjunction.
  End to_unit_counit.
End equivalences.

Coercion adjunction_unit__of__adjunction_unit_counit
: AdjunctionUnitCounit >-> AdjunctionUnit.
Coercion adjunction_counit__of__adjunction_unit_counit
: AdjunctionUnitCounit >-> AdjunctionCounit.
