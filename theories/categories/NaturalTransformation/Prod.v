(** * Natural transformations involving product categories *)
Require Import Category.Core Functor.Core Category.Prod Functor.Prod NaturalTransformation.Core.
Require Functor.Composition.Core Functor.Identity.
Require Import InitialTerminalCategory.Core.
Require Import types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

(** ** Product of natural transformations *)
Section prod.
  Context {A : PreCategory}.
  Context {B : PreCategory}.
  Context {C : PreCategory}.
  Variables F F' : Functor A B.
  Variables G G' : Functor A C.
  Variable T : NaturalTransformation F F'.
  Variable U : NaturalTransformation G G'.

  Definition prod
  : NaturalTransformation (F * G) (F' * G')
    := Build_NaturalTransformation
         (F * G) (F' * G')
         (fun x : A => (T x, U x))
         (fun _ _ _ => path_prod' (commutes T _ _ _) (commutes U _ _ _)).
End prod.

Local Infix "*" := prod : natural_transformation_scope.

(** ** Natural transformations between partially applied functors *)
Section induced.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variable F : Functor (C * D) E.

  Local Ltac t :=
    simpl; intros;
    rewrite <- !composition_of;
    simpl;
    rewrite ?left_identity, ?right_identity;
    reflexivity.

  Definition induced_fst s d (m : morphism C s d)
  : NaturalTransformation (Functor.Prod.induced_snd F s)
                          (Functor.Prod.induced_snd F d).
  Proof.
    let F0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(F0) end in
    let G0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(G0) end in
    refine (Build_NaturalTransformation
              F0 G0
              (fun d => @morphism_of _ _ F (_, _) (_, _) (m, @identity D d))
              _).
    abstract t.
  Defined.

  Definition induced_snd s d (m : morphism D s d)
  : NaturalTransformation (Functor.Prod.induced_fst F s)
                          (Functor.Prod.induced_fst F d).
  Proof.
    let F0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(F0) end in
    let G0 := match goal with |- NaturalTransformation ?F0 ?G0 => constr:(G0) end in
    refine (Build_NaturalTransformation
              F0 G0
              (fun c => @morphism_of _ _ F (_, _) (_, _) (@identity C c, m))
              _).
    abstract t.
  Defined.
End induced.

Module Export NaturalTransformationProdNotations.
  Infix "*" := prod : natural_transformation_scope.
End NaturalTransformationProdNotations.
