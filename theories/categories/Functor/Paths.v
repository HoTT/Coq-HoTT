Require Import Category.Core Functor.Core.
Require Import HProp HoTT.Tactics Equivalences PathGroupoids types.Sigma Trunc types.Record.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section path_functor.
  Context `{Funext}.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Local Open Scope equiv_scope.

  Local Notation functor_sig_T :=
    { OO : C -> D
    | { MO : forall s d, morphism C s d -> morphism D (OO s) (OO d)
      | { FCO : forall s d d' (m1 : morphism C s d) (m2 : morphism C d d'),
                  MO _ _ (m2 o m1) = MO d d' m2 o MO s d m1
        | forall x,
            MO x x (identity x) = identity (OO x) } } }
      (only parsing).

  Lemma equiv_sig_functor
  : functor_sig_T <~> Functor C D.
  Proof.
    issig (@Build_Functor C D) (@object_of C D) (@morphism_of C D) (@composition_of C D) (@identity_of C D).
  Defined.

  (** We could leave it at that and be done with it, but we want a more convenient form for actually constructing paths between functors.  For this, we write a trimmed down version of something equivalent to the type of paths between functors. *)

  Local Notation path_functor'_T F G
    := { HO : object_of F = object_of G
       | transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                   HO
                   (morphism_of F)
         = morphism_of G }
         (only parsing).

  (** We could just go prove that the path space of [functor_sig_T] is equivalent to [path_functor'_T], but unification is far too slow to do this effectively.  So instead we explicitly classify [path_functor'_T], and provide an equivalence between it and the path space of [Functor C D]. *)

  (*Definition equiv_path_functor'_sig_sig (F G : Functor C D)
  : path_functor'_T F G <~> (@equiv_inv _ _ _ equiv_sig_functor F
                              = @equiv_inv _ _ _ equiv_sig_functor G).
  Proof.
    etransitivity; [ | by apply equiv_path_sigma ].
    eapply @equiv_functor_sigma.
    repeat match goal with
             | [ |- appcontext[(@equiv_inv ?A ?B ?f ?H ?F).1] ]
               => change ((@equiv_inv A B f H F).1) with (object_of F)
           end.
    exact (isequiv_idmap (object_of F = object_of G)).
  Abort.*)

  Definition path_functor'_sig (F G : Functor C D) : path_functor'_T F G -> F = G.
  Proof.
    intros [? ?].
    destruct F, G; simpl in *.
    path_induction; simpl.
    f_ap;
      eapply @center; abstract exact _.
  Defined.

  Lemma path_functor'_sig_fst F G HO HM
  : ap object_of (@path_functor'_sig F G (HO; HM)) = HO.
  Proof.
    destruct F, G; simpl in *.
    path_induction_hammer.
  Qed.

  Lemma path_functor'_sig_idpath F
  : @path_functor'_sig F F (idpath; idpath) = idpath.
  Proof.
    destruct F; simpl in *.
    rewrite !(contr idpath).
    reflexivity.
  Qed.

  Definition path_functor'_sig_inv (F G : Functor C D) : F = G -> path_functor'_T F G
    := fun H'
       => (ap object_of H';
           (transport_compose _ _ _ _) ^ @ apD (@morphism_of _ _) H')%path.

  Lemma path_functor' (F G : Functor C D)
  : forall HO : object_of F = object_of G,
      transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d)) HO (morphism_of F) = morphism_of G
      -> F = G.
  Proof.
    intros.
    apply path_functor'_sig.
    esplit; eassumption.
  Defined.

  Lemma path_functor (F G : Functor C D)
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
    eapply (path_functor' F G (path_forall _ _ HO)).
    repeat (apply path_forall; intro); apply_hyp.
  Defined.

  Lemma equiv_path_functor'_sig (F G : Functor C D)
  : path_functor'_T F G <~> F = G.
  Proof.
    apply (equiv_adjointify (@path_functor'_sig F G)
                            (@path_functor'_sig_inv F G)).
    - hnf.
      intros [].
      apply path_functor'_sig_idpath.
    - hnf.
      intros [? ?].
      apply path_sigma_uncurried.
      exists (path_functor'_sig_fst _ _ _).
      exact (center _).
  Defined.

  Global Instance trunc_functor `{IsTrunc n D} `{forall s d, IsTrunc n (morphism D s d)}
  : IsTrunc n (Functor C D).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_functor | ].
    induction n;
    simpl; intros;
    typeclasses eauto.
  Qed.
End path_functor.

Ltac path_functor :=
  repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => apply path_functor'_sig; simpl
           | _ => (exists idpath)
         end.

Global Arguments path_functor'_sig : simpl never.
