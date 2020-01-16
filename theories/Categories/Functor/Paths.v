(** * Classification of path spaces of functors *)
Require Import Category.Core Functor.Core.
Require Import HoTT.Basics HoTT.Types HoTT.Tactics Equivalences HProp.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section path_functor.
  Context `{Funext}.

  Variables C D : PreCategory.



  Local Notation functor_sig_T :=
    { OO : C -> D
    | { MO : forall s d, morphism C s d -> morphism D (OO s) (OO d)
      | { FCO : forall s d d' (m1 : morphism C s d) (m2 : morphism C d d'),
                  MO _ _ (m2 o m1) = MO d d' m2 o MO s d m1
        | forall x,
            MO x x (identity x) = identity (OO x) } } }
      (only parsing).

  (** ** Equivalence between the record and sigma-type versions of a functor *)
  Lemma equiv_sig_functor
  : functor_sig_T <~> Functor C D.
  Proof.
    issig.
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

  (**
<<
  Definition equiv_path_functor_uncurried_sig (F G : Functor C D)
  : path_functor'_T F G <~> (@equiv_inv _ _ _ equiv_sig_functor F
                              = @equiv_inv _ _ _ equiv_sig_functor G).
  Proof.
    etransitivity; [ | by apply equiv_path_sigma ].
    eapply @equiv_functor_sigma.
    repeat match goal with
             | [ |- context[(@equiv_inv ?A ?B ?f ?H ?F).1] ]
               => change ((@equiv_inv A B f H F).1) with (object_of F)
           end.
    Time exact (isequiv_idmap (object_of F = object_of G)). (* 13.411 secs *)
  Abort.
>>
   *)

  (** ** Classify sufficient conditions to prove functors equal *)
  Definition path_functor_uncurried (F G : Functor C D) : path_functor'_T F G -> F = G.
  Proof.
    intros [? ?].
    destruct F, G; simpl in *.
    path_induction; simpl.
    f_ap;
      eapply @center; abstract exact _.
  Defined.

  (** *** Said proof respects [object_of] *)
  Lemma path_functor_uncurried_fst F G HO HM
  : ap object_of (@path_functor_uncurried F G (HO; HM)) = HO.
  Proof.
    destruct F, G; simpl in *.
    path_induction_hammer.
  Qed.

  (** *** Said proof respects [idpath] *)
  Lemma path_functor_uncurried_idpath F
  : @path_functor_uncurried F F (idpath; idpath) = idpath.
  Proof.
    destruct F; simpl in *.
    rewrite !(contr idpath).
    reflexivity.
  Qed.

  (** ** Equality of functors gives rise to an inhabitant of the path-classifying-type *)
  Definition path_functor_uncurried_inv (F G : Functor C D) : F = G -> path_functor'_T F G
    := fun H'
       => (ap object_of H';
           (transport_compose _ object_of _ _) ^ @ apD (@morphism_of _ _) H')%path.

  (** ** Curried version of path classifying lemma *)
  Definition path_functor (F G : Functor C D)
        (HO : object_of F = object_of G)
        (HM : transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d)) HO (morphism_of F) = morphism_of G)
  : F = G
    := path_functor_uncurried F G (HO; HM).

  (** ** Curried version of path classifying lemma, using [forall] in place of equality of functions *)
  Definition path_functor_pointwise (F G : Functor C D)
        (HO : object_of F == object_of G)
        (HM : forall s d m,
                transport (fun GO => forall s d, morphism C s d -> morphism D (GO s) (GO d))
                          (path_forall _ _ HO)
                          (morphism_of F)
                          s d m
                = G _1 m)
  : F = G.
  Proof.
    refine (path_functor F G (path_forall _ _ HO) _).
    repeat (apply path_forall; intro); apply HM.
  Defined.

  (** ** Classify equality of functors up to equivalence *)
  Global Instance isequiv_path_functor_uncurried (F G : Functor C D)
  : IsEquiv (@path_functor_uncurried F G).
  Proof.
    apply (isequiv_adjointify (@path_functor_uncurried F G)
                              (@path_functor_uncurried_inv F G)).
    - hnf.
      intros [].
      apply path_functor_uncurried_idpath.
    - hnf.
      intros [? ?].
      apply path_sigma_uncurried.
      exists (path_functor_uncurried_fst _ _ _).
      exact (center _).
  Defined.

  Definition equiv_path_functor_uncurried (F G : Functor C D)
  : path_functor'_T F G <~> F = G
    := Build_Equiv _ _ (@path_functor_uncurried F G) _.

  Local Open Scope function_scope.

  Definition path_path_functor_uncurried (F G : Functor C D) (p q : F = G)
  : ap object_of p = ap object_of q -> p = q.
  Proof.
    refine ((ap (@path_functor_uncurried F G)^-1)^-1 o _).
    refine ((path_sigma_uncurried _ _ _) o _); simpl.
    refine (pr1^-1).
  Defined.

  Global Instance isequiv_path_path_functor_uncurried F G p q
  : IsEquiv (@path_path_functor_uncurried F G p q).
  Proof.
    unfold path_path_functor_uncurried.
    (** N.B. [exact _] is super-slow here.  Not sure why. *)
    repeat match goal with
             | [ |- IsEquiv (_ o _) ] => eapply @isequiv_compose
             | [ |- IsEquiv (_^-1) ] => eapply @isequiv_inverse
             | [ |- IsEquiv (path_sigma_uncurried _ _ _) ] => eapply @isequiv_path_sigma
             | _ => apply @isequiv_compose
           end.
  Defined.

  (** ** If the objects in [D] are n-truncated, then so is the type of functors [C → D] *)
  Global Instance trunc_functor `{IsTrunc n D} `{forall s d, IsTrunc n (morphism D s d)}
  : IsTrunc n (Functor C D).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_functor | ].
    induction n;
    simpl; intros;
    typeclasses eauto.
  Qed.
End path_functor.

(** ** Tactic for proving equality of functors *)
Ltac path_functor :=
  repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => apply path_functor_uncurried; simpl
           | _ => (exists idpath)
         end.

Global Arguments path_functor_uncurried : simpl never.

(** ** Tactic for pushing [ap object_of] through other [ap]s.

    This allows lemmas like [path_functor_uncurried_fst] to apply more
    easily. *)
Ltac push_ap_object_of' :=
  idtac;
  match goal with
    | [ |- context[ap object_of (ap ?f ?p)] ]
      => rewrite <- (ap_compose' f object_of p); simpl
    | [ |- context G[ap (fun F' x => object_of F' (@?f x)) ?p] ]
      => let P := context_to_lambda G in
         refine (transport P (ap_compose' object_of (fun F' x => F' (f x)) p)^ _)
    | [ |- context G[ap (fun F' x => ?f (object_of F' x)) ?p] ]
      => let P := context_to_lambda G in
         refine (transport P (ap_compose' object_of (fun F' x => f (F' x)) p)^ _)
  end.
Ltac push_ap_object_of := repeat push_ap_object_of'.
