Require Export Functor.Core.
Require Import HProp HoTT.Tactics Equivalences PathGroupoids types.Sigma Trunc.

Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section Functors_Equal.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Open Scope equiv_scope.


  Local Notation Functor_eq'_T F G
    := { HO : object_of F = object_of G
       | transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                   HO
                   (morphism_of F)
         = morphism_of G }
         (only parsing).

  Definition Functor_eq'_sig (F G : Functor C D) : Functor_eq'_T F G -> F = G.
  Proof.
    intros [? ?].
    destruct F, G; simpl in *.
    path_induction; simpl.
    f_ap;
      abstract exact (center _).
  Defined.

  Lemma Functor_eq'_sig_fst F G HO HM
  : ap object_of (@Functor_eq'_sig F G (HO; HM)) = HO.
  Proof.
    destruct F, G; simpl in *.
    path_induction_hammer.
  Qed.

  Lemma Functor_eq'_sig_idpath F
  : @Functor_eq'_sig F F (idpath; idpath) = idpath.
  Proof.
    destruct F; simpl in *.
    path_induction_hammer.
  Qed.

  Definition Functor_eq'_sig_inv (F G : Functor C D) : F = G -> Functor_eq'_T F G
    := fun H'
       => (ap object_of H';
           (transport_compose _ _ _ _) ^ @ apD (@morphism_of _ _) H')%path.

  Lemma Functor_eq' (F G : Functor C D)
  : forall HO : object_of F = object_of G,
      transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d)) HO (morphism_of F) = morphism_of G
      -> F = G.
  Proof.
    intros.
    apply Functor_eq'_sig.
    esplit; eassumption.
  Defined.

  Lemma Functor_eq (F G : Functor C D)
  : forall HO : object_of F == object_of G,
      (forall s d m,
         transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                   (path_forall _ _ HO)
                   (morphism_of F)
                   s d m
         = morphism_of G m)
      -> F = G.
  Proof.
    intros.
    eapply (Functor_eq' F G (path_forall _ _ HO)).
    repeat (apply path_forall; intro); apply_hyp.
  Qed.

(*  Local Ltac t :=
    repeat match goal with
             | _ => reflexivity
             | _ => intro
             | _ => progress path_induction
             | _ => progress destruct_head Functor
             | _ => progress simpl in *
             | _ => progress destruct_eq_in_match
             | _ => progress destruct_head sigT
             | _ => progress step_clear_paths_in_match
           end.*)

  Lemma Functor_eq'_sig_equiv (F G : Functor C D)
  : Functor_eq'_T F G <~> F = G.
  Proof.
    apply (equiv_adjointify (@Functor_eq'_sig F G)
                            (@Functor_eq'_sig_inv F G)).
    - hnf.
      intros [].
      apply Functor_eq'_sig_idpath.
    - hnf.
      intros [? ?].
      apply path_sigma_uncurried.
      exists (Functor_eq'_sig_fst _ _ _).
      exact (center _).
  Defined.

  (*Lemma Functor_sig
  : { OO : C -> D
    & { MO : forall s d, morphism C s d -> morphism D (OO s) (OO d)
      & { FCO : forall s d d' (m1 : morphism C s d) (m2 : morphism C d d'),
                  MO _ _ (m2 ∘ m1) = MO d d' m2 ∘ MO s d m1
        & forall x,
            MO x x (identity x) = identity (OO x) } } }
      <~> Functor C D.
  Proof.
    issig (@Build_Functor C D) (@object_of C D) (@morphism_of C D) (@composition_of C D) (@identity_of C D).
  Defined.*)

  Global Instance Functor_IsTrunc `{IsTrunc n D} `{forall s d, IsTrunc n (morphism D s d)}
  : IsTrunc n (Functor C D).
  Proof.
    induction n;
    simpl; intros;
    [ refine {| center
                := (Build_Functor
                      C D
                      (fun _ => center D)
                      (fun _ _ _ => identity _)
                      (fun _ _ _ _ _ => symmetry _ _ (identity_identity D _))
                      (fun _ => idpath)) |};
      intros;
      match goal with
        | [ |- ?F = ?G ] => apply (Functor_eq F G (fun _ => contr _))
      end;
      simpl; intros;
      refine (center _)
    | intros ? ?; eapply trunc_equiv';
      [ exact (Functor_eq'_sig_equiv _ _)
      | typeclasses eauto ]
    ].
  Defined.
End Functors_Equal.

Ltac functor_eq :=
  repeat match goal with
           | _ => intro
           | _ => apply Functor_eq'_sig; simpl
           | _ => (exists idpath)
         end.
