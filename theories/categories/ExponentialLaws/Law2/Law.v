(** * Exponential laws about products and sums in exponents *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import ExponentialLaws.Law2.Functors.
Require Import Functor.Pointwise Functor.Prod.
Require Import Category.Sum Functor.Sum NaturalTransformation.Sum.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Functor.Identity Functor.Composition.Core.
Require Import types.Prod HoTT.Tactics types.Forall PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

(** ** [yⁿ⁺ᵐ ≅ yⁿ × yᵐ] *)
Section Law2.
  Context `{Funext}.
  Variable D : PreCategory.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.

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
    abstract (
        repeat (apply (@path_forall _); intro);
        repeat match goal with
                 | [ H : Empty |- _ ] => by destruct H
                 | _ => reflexivity
                 | [ H : (_ + _)%type |- _ ] => destruct H
                 | [ |- appcontext[transport (fun x : ?A => forall y : ?B, @?C x y) ?p ?f ?k] ]
                   => simpl rewrite (@transport_forall_constant A B C _ _ p f k)
                 | _ => progress transport_path_forall_hammer
               end
      ).
  Defined.

  Lemma law
  : functor D C1 C2 o inverse D C1 C2 = 1
    /\ inverse D C1 C2 o functor D C1 C2 = 1.
  Proof.
    split;
    path_functor;
    [ (exists (path_forall _ _ helper1))
    | (exists (path_forall _ _ helper2)) ];
    repeat (apply (@path_forall _) || apply path_prod || intro || path_functor || path_natural_transformation);
    destruct_head prod;
    rewrite !transport_forall_constant;
    transport_path_forall_hammer;
    unfold helper1, helper2;
    repeat match goal with
             | _ => progress simpl in *
             | _ => reflexivity
             | [ H : (_ * _)%type |- _ ] => destruct H
             | [ H : (_ + _)%type |- _ ] => destruct H
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
             | [ |- appcontext[ap (@object_of ?C ?D) (@path_functor'_sig ?H ?C ?D ?F ?G (?HO; ?HM))] ]
               => simpl rewrite (@path_functor'_sig_fst H C D F G HO HM)
             | _ => transport_path_forall_hammer
           end.
  Qed.
End Law2.
