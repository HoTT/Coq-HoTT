(** * Law about currying *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Prod.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Functor.Identity Functor.Composition.Core.
Require Import ExponentialLaws.Law4.Functors.
Require Import types.Prod HoTT.Tactics types.Forall PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

(** ** [(C₁ × C₂ → D) ≅ (C₁ → (C₂ → D))] *)
Section Law4.
  Context `{Funext}.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Lemma helper1 c
  : functor C1 C2 D (inverse C1 C2 D c) = c.
  Proof.
    path_functor.
    abstract (
        simpl;
        repeat (apply path_forall || intro);
        rewrite <- composition_of;
        simpl;
        autorewrite with morphism;
        reflexivity
      ).
  Defined.

  Lemma helper2_helper c x
  : inverse C1 C2 D (functor C1 C2 D c) x = c x.
  Proof.
    path_functor.
    abstract (
        repeat (apply path_forall || intro);
        rewrite !transport_forall_constant;
        simpl;
        rewrite identity_of; simpl;
          by autorewrite with morphism
      ).
  Defined.

  Local Ltac exp_t :=
    repeat match goal with
             | _ => progress simpl in *
             | _ => reflexivity
             | _ => rewrite !identity_of
             | _ => progress autorewrite with morphism
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
             | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x) ?k))] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x) k)) (@object_of C D))
             | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x) ?k) ?z)] ]
               => rewrite (fun a b => @transport_compose _ _ a b (fun y => f (g (y x) k) z) (@object_of C D))
             | [ |- appcontext[ap (@object_of ?C ?D) (@path_functor'_sig ?H ?C ?D ?F ?G (?HO; ?HM))] ]
               => simpl rewrite (@path_functor'_sig_fst H C D F G HO HM)
             | _ => transport_path_forall_hammer
           end.

  Lemma helper2 c
  : inverse C1 C2 D (functor C1 C2 D c) = c.
  Proof.
    path_functor.
    exists (path_forall _ _ (helper2_helper c)).
    abstract (
        repeat (apply path_forall || intro || path_natural_transformation);
        rewrite !transport_forall_constant;
        simpl;
        transport_path_forall_hammer;
        unfold helper2_helper;
        simpl;
        exp_t
      ).
  Defined.

  Lemma law
  : functor C1 C2 D o inverse C1 C2 D = 1
    /\ inverse C1 C2 D o functor C1 C2 D = 1.
  Proof.
    split;
    path_functor;
    [ (exists (path_forall _ _ helper1))
    | (exists (path_forall _ _ helper2)) ];
    repeat (apply path_forall || intro || path_natural_transformation);
    rewrite !transport_forall_constant;
    unfold helper1, helper2, helper2_helper;
    destruct_head Datatypes.prod.
    - exp_t.
    - exp_t.
  Qed.
End Law4.
