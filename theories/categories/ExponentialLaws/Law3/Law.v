(** * Laws about an exponential of a product and a product of exponentials *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Prod Functor.Prod.Functorial Functor.Prod.Universal.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Functor.Identity Functor.Composition.Core.
Require Import ExponentialLaws.Law3.Functors.
Require Import types.Prod HoTT.Tactics types.Forall PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

(** ** [(y × z)ⁿ ≅ yⁿ × zⁿ] *)
Section Law3.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Lemma helper (c : Functor D C1 * Functor D C2)
  : ((fst o (Datatypes.fst c * Datatypes.snd c))%functor,
     (snd o (Datatypes.fst c * Datatypes.snd c))%functor)%core = c.
  Proof.
    apply path_prod;
    [ apply compose_fst_prod
    | apply compose_snd_prod ].
  Defined.

  Lemma Law
  : functor C1 C2 D o inverse C1 C2 D = 1
    /\ inverse C1 C2 D o functor C1 C2 D = 1.
  Proof.
    split; path_functor;
    [ (exists (path_forall _ _ helper));
      repeat (apply path_forall || intros [? ?])
    | (exists (path_forall _ _ (fun _ => Functor.Prod.Universal.unique idpath idpath)));
      repeat (apply path_forall || intro) ];
    rewrite !transport_forall_constant;
    transport_path_forall_hammer;
    repeat (apply path_prod || path_natural_transformation || simpl);
    unfold helper, compose_fst_prod, compose_snd_prod, Functor.Prod.Universal.unique, Functor.Prod.Universal.unique_helper;
    repeat match goal with
             | _ => progress simpl in *
             | _ => reflexivity
             | [ |- appcontext[Datatypes.fst (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @Datatypes.fst _ _) z)
             | [ |- appcontext[Datatypes.snd (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @Datatypes.snd _ _) z)
             | [ |- appcontext[components_of (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => components_of) z)
             | _ => rewrite !transport_path_prod
             | _ => rewrite !transport_const
             | _ => rewrite !transport_forall_constant
             | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x)) (@object_of C D))
             | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (y x) z) (@object_of C D))
             | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x)))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x))) (@object_of C D))
             | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x)) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x)) z) (@object_of C D))
             | [ |- appcontext[ap (@object_of ?C ?D) (@path_functor'_sig ?H ?C ?D ?F ?G (?HO; ?HM))] ]
               => simpl rewrite (@path_functor'_sig_fst H C D F G HO HM)
             | _ => transport_path_forall_hammer
           end.
  Qed.
End Law3.
