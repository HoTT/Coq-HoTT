(** * Exponential laws about products and sums in exponents *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Pointwise.Core Functor.Prod.Core.
Require Import Category.Sum Functor.Sum NaturalTransformation.Sum.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Functor.Identity Functor.Composition.Core.
Require Import Types.Prod HoTT.Tactics ExponentialLaws.Tactics.
Require Import ExponentialLaws.Law2.Functors.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

(** ** [yⁿ⁺ᵐ ≅ yⁿ × yᵐ] *)
Section Law2.
  Context `{Funext}.
  Variables D C1 C2 : PreCategory.



  Lemma helper1 (c : Functor C1 D * Functor C2 D)
  : ((1 o (Datatypes.fst c + Datatypes.snd c) o inl C1 C2)%functor,
     (1 o (Datatypes.fst c + Datatypes.snd c) o inr C1 C2)%functor)%core = c.
  Proof.
    apply path_prod; simpl;
    path_functor.
  Defined.

  Lemma helper2_helper (c : Functor (C1 + C2) D) x
  : (1 o c o inl C1 C2 + 1 o c o inr C1 C2) x = c x.
  Proof.
    destruct x; reflexivity.
  Defined.

  Lemma helper2 (c : Functor (C1 + C2) D)
  : 1 o c o inl C1 C2 + 1 o c o inr C1 C2 = c.
  Proof.
    path_functor.
    (exists (path_forall _ _ (@helper2_helper c))).
    abstract exp_laws_t.
  Defined.

  Lemma law
  : functor D C1 C2 o inverse D C1 C2 = 1
    /\ inverse D C1 C2 o functor D C1 C2 = 1.
  Proof.
    split;
    path_functor;
    [ (exists (path_forall _ _ helper1))
    | (exists (path_forall _ _ helper2)) ];
    exp_laws_t;
    unfold helper1, helper2;
    exp_laws_t.
  Qed.
End Law2.
