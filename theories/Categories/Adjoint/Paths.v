(** * Classify the path space of adjunctions *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core Functor.Identity.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import Adjoint.UnitCounit Adjoint.Core NaturalTransformation.Paths.
Require Import Types.Record Types.Sigma Trunc.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section path_adjunction.
  Context `{Funext}.

  Variables C D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.



  Notation adjunction_sigT :=
    { eta : NaturalTransformation 1 (G o F)
    | { eps : NaturalTransformation (F o G) 1
      | { equ1 : forall Y : C, (eps (F Y) o F _1 (eta Y))%morphism = 1%morphism
        | forall X : D, (G _1 (eps X) o eta (G X))%morphism = 1%morphism }}}.

  (** ** Equivalence between record and nested sigma for unit+counit adjunctions *)
  Lemma equiv_sig_adjunction
  : adjunction_sigT <~> (F -| G).
  Proof.
    issig.
  Defined.

  (** ** Adjunctions are an hSet *)
  Global Instance trunc_adjunction : IsHSet (F -| G).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_adjunction | ].
    typeclasses eauto.
  Qed.

  (** ** Equality of adjunctions follows from equality of unit+counit *)
  Lemma path_adjunction' (A A' : F -| G)
  : unit A = unit A'
    -> counit A = counit A'
    -> A = A'.
  Proof.
    intros.
    destruct A, A'; simpl in *.
    path_induction.
    f_ap;
      exact (center _).
  Qed.

  (** ** Equality of adjunctions follows from equality of action of unit+counit on objects *)
  Lemma path_adjunction (A A' : F -| G)
  : components_of (unit A) == components_of (unit A')
    -> components_of (counit A) == components_of (counit A')
    -> A = A'.
  Proof.
    intros.
    apply path_adjunction';
    apply path_natural_transformation;
    assumption.
  Qed.

  (** In fact, it suffices to show that either the units are equal, or
      the counits are equal, by the UMP of the (co)unit.  And if we
      are working in a [Category], rather than a [PreCategory], then
      [Adjunction] is, in fact, an hProp, because the (co)unit is
      unique up to unique isomorphism.

      TODO: Formalize this. *)
End path_adjunction.

Ltac path_adjunction :=
  repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => apply path_adjunction; simpl
         end.
