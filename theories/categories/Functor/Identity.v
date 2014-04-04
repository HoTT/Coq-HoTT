Require Import Category.Core Functor.Core.
Require Import Category.Morphisms.
Require Import PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

Section identity.
  (** We first define a generalized identity functor. *)
  Section generalized.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Hypothesis HO : object C = object D.
    Hypothesis HM : transport (fun objC => objC -> objC -> Type)
                              HO
                              (morphism C)
                    = morphism D.
    Hypothesis HC : transport (fun morC => forall s d d', morC d d' -> morC s d -> morC s d')
                              HM
                              (transportD (fun objC => objC -> objC -> Type)
                                          (fun objC morC => forall s d d', morC d d' -> morC s d -> morC s d')
                                          HO
                                          (morphism C)
                                          (@compose C))
                    = @compose D.

    Definition generalized_identity_generic_Hid x
    : transport (fun morC => forall x, morC x x)
                HM
                (transportD (fun objC => objC -> objC -> Type)
                            (fun objC morC => forall x, morC x x)
                            HO
                            (morphism C)
                            (@identity C)) x
      = @identity D x.
    Proof.
      generalize (@left_identity D).
      generalize (@identity D).
      revert x.
      case HC. case HM. case HO.
      simpl.
      intros.
      apply identity_unique;
        [ assumption
        | intros;
          apply right_identity ].
    Defined.

    Hypothesis Hid
    : forall x,
        transport (fun morC => forall x, morC x x)
                  HM
                  (transportD (fun objC => objC -> objC -> Type)
                              (fun objC morC => forall x, morC x x)
                              HO
                              (morphism C)
                              (@identity C)) x
        = @identity D x.

    Local Notation CO c := (transport (fun obj => obj)
                                      HO
                                      c).

    Local Notation CM s d m :=
      (transport (fun mor => mor (CO s) (CO d))
                 HM
                 (match HO as HO' in (_ = obj)
                        return (transport (fun objC => objC -> objC -> Type)
                                          HO'
                                          (morphism C)
                                          (transport (fun obj => obj) HO' s)
                                          (transport (fun obj => obj) HO' d))
                  with
                    | idpath => m
                  end)).

    Definition generalized_identity_composition_of
               s d d' (m1 : morphism C s d) (m2 : morphism C d d')
    : CM _ _ (m2 o m1) = CM _ _ m2 o CM _ _ m1.
    Proof.
      case HC. case HM. case HO.
      reflexivity.
    Defined.

    Local Notation CM_id :=
      (fun x : D =>
         (idtoiso D (transport_pV idmap HO _) : morphism D _ _)
           o (CM (transport (fun obj => obj) HO^ x) _ 1)
           o (idtoiso D (transport_pV idmap HO _)^ : morphism D _ _)%path
         : morphism D x x).

    Definition generalized_identity_identity_of x
    : CM x x 1 = 1.
    Proof.
      case Hid. case HM. case HO.
      reflexivity.
    Defined.

    Definition generalized_identity : Functor C D
      := Build_Functor
           C D
           (fun x => CO x)
           (fun s d m => CM s d m)
           generalized_identity_composition_of
           generalized_identity_identity_of.
  End generalized.

  Global Arguments generalized_identity_identity_of / .
  Global Arguments generalized_identity_composition_of / .
  Global Arguments generalized_identity C D !HO !HM !HC Hid / .

  Section generalized'.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Hypothesis H : C = D.

    Definition generalized_identity' : Functor C D.
    Proof.
      case H.
      apply (generalized_identity C C idpath idpath idpath (fun x => idpath)).
    Defined.
  End generalized'.

  Global Arguments generalized_identity' C D !H / .

  (** There is an identity functor.  It does the obvious thing. *)
  Definition identity C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End identity.

Module Export FunctorIdentityNotations.
  Notation "1" := (identity _) : functor_scope.
End FunctorIdentityNotations.
