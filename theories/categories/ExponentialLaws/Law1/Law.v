(** * Exponential laws about the terminal category *)
Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Identity NaturalTransformation.Core Functor.Paths NaturalTransformation.Paths ExponentialLaws.Law1.Functors Functor.Composition.Core.
Require Import InitialTerminalCategory.Core.
Require Import HoTT.Tactics types.Forall types.Prod PathGroupoids.

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
        repeat (apply path_forall; intro);
        rewrite !transport_forall_constant;
        simpl;
        transport_path_forall_hammer;
        repeat match goal with
                 | [ H : object 1 |- _ ] => destruct (contr H)
                 | [ H : morphism 1 _ _ |- _ ] => destruct (contr H)
               end;
        simpl;
        rewrite <- identity_of;
        f_ap;
        apply symmetry;
        apply contr
      ).
  Defined.

  Lemma law
  : functor C o inverse C = 1
    /\ inverse C o functor C = 1.
  Proof.
    split;
    path_functor.
    exists (path_forall _ _ helper).
    repeat (apply (@path_forall _) || intro || path_functor || path_natural_transformation).
    repeat match goal with
             | _ => reflexivity
             | _ => progress simpl
             | [ H : object 1 |- _ ] => destruct (contr H)
             | [ H : morphism 1 _ _ |- _ ] => destruct (contr H)
             | _ => rewrite !transport_forall_constant
             | [ |- appcontext[components_of (transport ?P ?p ?z)] ]
               => rewrite (@ap_transport _ P _ _ _ p (fun _ => components_of) z)
             | _ => rewrite path_forall_2_beta, ?transport_const
             | _ => transport_path_forall_hammer
           end.
    unfold helper.
    repeat match goal with
             | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x)) (@object_of C D))
             | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x) z) (@object_of C D))
           end.
    rewrite !path_functor'_sig_fst.
    transport_path_forall_hammer.
    assert (idpath = contr (center 1%category)) by exact (center _).
    path_induction.
    reflexivity.
  Qed.
End law1.
