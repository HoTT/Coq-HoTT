Require Export Functor.Core.
Require Import HProp HoTT.Tactics Equivalences PathGroupoids types.Sigma Trunc types.Record.

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

  Local Notation paths'_functor_T F G
    := { HO : object_of F = object_of G
       | transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                   HO
                   (morphism_of F)
         = morphism_of G }
         (only parsing).

  (** We could just go prove that the path space of [functor_sig_T] is equivalent to [paths'_functor_T], but unification is far too slow to do this effectively.  So instead we explicitly classify [paths'_functor_T], and provide an equivalence between it and the path space of [Functor C D]. *)

  (*Definition equiv_paths'_functor_sig_sig (F G : Functor C D)
  : paths'_functor_T F G <~> (@equiv_inv _ _ _ equiv_sig_functor F
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

  Definition paths'_functor_sig (F G : Functor C D) : paths'_functor_T F G -> F = G.
  Proof.
    intros [? ?].
    destruct F, G; simpl in *.
    path_induction; simpl.
    f_ap;
      abstract exact (center _).
  Defined.

  Lemma paths'_functor_sig_fst F G HO HM
  : ap object_of (@paths'_functor_sig F G (HO; HM)) = HO.
  Proof.
    destruct F, G; simpl in *.
    path_induction_hammer.
  Qed.

  Lemma paths'_functor_sig_idpath F
  : @paths'_functor_sig F F (idpath; idpath) = idpath.
  Proof.
    destruct F; simpl in *.
    path_induction_hammer.
  Qed.

  Definition paths'_functor_sig_inv (F G : Functor C D) : F = G -> paths'_functor_T F G
    := fun H'
       => (ap object_of H';
           (transport_compose _ _ _ _) ^ @ apD (@morphism_of _ _) H')%path.

  Lemma paths'_functor (F G : Functor C D)
  : forall HO : object_of F = object_of G,
      transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d)) HO (morphism_of F) = morphism_of G
      -> F = G.
  Proof.
    intros.
    apply paths'_functor_sig.
    esplit; eassumption.
  Defined.

  Lemma paths_functor (F G : Functor C D)
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
    eapply (paths'_functor F G (path_forall _ _ HO)).
    repeat (apply path_forall; intro); apply_hyp.
  Defined.

  Lemma equiv_paths'_functor_sig (F G : Functor C D)
  : paths'_functor_T F G <~> F = G.
  Proof.
    apply (equiv_adjointify (@paths'_functor_sig F G)
                            (@paths'_functor_sig_inv F G)).
    - hnf.
      intros [].
      apply paths'_functor_sig_idpath.
    - hnf.
      intros [? ?].
      apply path_sigma_uncurried.
      exists (paths'_functor_sig_fst _ _ _).
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
End Functors_Equal.

Ltac paths_functor :=
  repeat match goal with
           | _ => intro
           | _ => apply paths'_functor_sig; simpl
           | _ => (exists idpath)
         end.
