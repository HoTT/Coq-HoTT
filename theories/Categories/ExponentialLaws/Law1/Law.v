(** * Exponential laws about the terminal category *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.FunctorCategory.Core HoTT.Categories.Functor.Identity HoTT.Categories.NaturalTransformation.Core HoTT.Categories.Functor.Paths HoTT.Categories.NaturalTransformation.Paths HoTT.Categories.ExponentialLaws.Law1.Functors HoTT.Categories.Functor.Composition.Core.
Require Import HoTT.Categories.InitialTerminalCategory.Core.
Require Import HoTT.Basics.Trunc HoTT.Tactics HoTT.Categories.ExponentialLaws.Tactics.
Require Import HoTT.Basics.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

(** ** [C¹ ≅ C] *)
Section law1.
  Context `{Funext}.
  Context `{IsInitialCategory zero}.
  Context `{IsTerminalCategory one}.
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Definition helper (c : Functor 1 C)
  : Functors.from_terminal C (c (center _)) = c.
  Proof.
    path_functor.
    exists (path_forall _ _ (fun x => ap (object_of c) (contr _))).
    abstract (
        exp_laws_t;
        simpl;
        rewrite <- identity_of;
        f_ap;
        symmetry;
        apply contr
      ).
  Defined.

  Lemma law
  : @functor _ one _ C o inverse C = 1
    /\ inverse C o @functor _ one _ C = 1.
  Proof.
    split;
    path_functor.
    exists (path_forall _ _ helper).
    unfold helper.
    exp_laws_t.
  Qed.
End law1.
