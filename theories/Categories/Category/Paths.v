(** * Classification of path spaces of precategories *)
Require Import Category.Core.
Require Import HoTT.Basics.Equivalences HoTT.Basics.PathGroupoids HoTT.Basics.Trunc.
Require Import HoTT.Types.Sigma HoTT.Types.Record HoTT.Types.Arrow HoTT.Types.Forall HoTT.Types.Paths.
Require Import HoTT.HProp HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope category_scope.

Section path_category.
  Local Open Scope path_scope.


  (** We add a prime ([']) as an arbitrary convention to denote that
      we are talking about equality of functions (less convenient for
      use) rather than pointwise equality of functions (more
      convenient for use, but more annoying for proofs).  We add two
      primes to denote the even less convenient version, which
      requires an identity equality proof. *)
  Local Notation path_precategory''_T C D
    := { Hobj : object C = object D
       | { Hmor : transport (fun obj => obj -> obj -> Type)
                            Hobj
                            (morphism C)
                  = morphism D
         | transport _
                     Hmor
                     (transportD (fun obj => obj -> obj -> Type)
                                 (fun obj mor => forall s d d', mor d d' -> mor s d -> mor s d')
                                 Hobj
                                 (morphism C)
                                 (@compose C))
           = @compose D
           /\ transport _
                        Hmor
                        (transportD (fun obj => obj -> obj -> Type)
                                    (fun obj mor => forall x, mor x x)
                                    Hobj
                                    (morphism C)
                                    (@identity C))
              = @identity D }}.

  Local Notation path_precategory'_T C D
    := { Hobj : object C = object D
       | { Hmor : transport (fun obj => obj -> obj -> Type)
                            Hobj
                            (morphism C)
                  = morphism D
         | transport _
                     Hmor
                     (transportD (fun obj => obj -> obj -> Type)
                                 (fun obj mor => forall s d d', mor d d' -> mor s d -> mor s d')
                                 Hobj
                                 (morphism C)
                                 (@compose C))
           = @compose D }}.

  (** ** Classify sufficient conditions to prove precategories equal *)
  Lemma path_precategory_uncurried__identity_helper `{Funext} (C D : PreCategory)
        (Heq : path_precategory'_T C D)
  : transport _
              Heq.2.1
              (transportD (fun obj => obj -> obj -> Type)
                          (fun obj mor => forall x, mor x x)
                          Heq.1
                          (morphism C)
                          (@identity C))
    = @identity D.
  Proof.
    destruct Heq as [? [? ?]]; cbn in *.
    repeat (intro || apply path_forall).
    apply identity_unique; cbn in *; auto with morphism.
    destruct C, D; cbn in *.
    path_induction; cbn in *.
    auto.
  Qed.

  Definition path_precategory''_T__of__path_precategory'_T `{Funext} C D
  : path_precategory'_T C D -> path_precategory''_T C D
    := fun H => (H.1; (H.2.1; (H.2.2, path_precategory_uncurried__identity_helper C D H))).

  Lemma eta2_sigma_helper A B P Q `{forall a b, IsHProp (Q a b)}
        (x : { a : A & { b : B a & P a b /\ Q a b }})
        q'
  : (x.1; (x.2.1; (fst x.2.2, q'))) = x.
  Proof.
    destruct x as [? [? [? ?]]]; cbn in *.
    repeat f_ap; apply path_ishprop.
  Defined.

  Global Instance isequiv__path_precategory''_T__of__path_precategory'_T `{fs : Funext} C D
  : IsEquiv (@path_precategory''_T__of__path_precategory'_T fs C D)
    := isequiv_adjointify
         (@path_precategory''_T__of__path_precategory'_T fs C D)
         (fun H => (H.1; (H.2.1; fst H.2.2)))
         (fun x => eta2_sigma_helper _ _ _ x _)
         eta2_sigma.

  Definition path_precategory_uncurried' `{fs : Funext} (C D : PreCategory)
  : path_precategory''_T C D -> C = D.
  Proof.
    intros [? [? [? ?]]].
    destruct C, D; cbn in *.
    path_induction; cbn in *.
    f_ap;
      eapply @center; abstract exact _.
  Defined.

  (** *** Said proof respects [object] *)
  Lemma path_precategory_uncurried'_fst `{Funext} C D HO HM HC HI
  : ap object (@path_precategory_uncurried' _ C D (HO; (HM; (HC, HI)))) = HO.
  Proof.
    destruct C, D; cbn in *.
    path_induction_hammer.
  Qed.

  (** *** Said proof respects [idpath] *)
  Lemma path_precategory_uncurried'_idpath `{Funext} C
  : @path_precategory_uncurried' _ C C (idpath; (idpath; (idpath, idpath))) = idpath.
  Proof.
    destruct C; cbn in *.
    rewrite !(contr idpath).
    reflexivity.
  Qed.

  (** ** Equality of precategorys gives rise to an inhabitant of the path-classifying-type *)
  Definition path_precategory_uncurried'_inv (C D : PreCategory)
  : C = D -> path_precategory''_T C D.
  Proof.
    intro H'.
    exists (ap object H').
    exists ((transport_compose _ object _ _) ^ @ apD (@morphism) H').
    split.
    - refine (_ @ apD (@compose) H'); cbn.
      refine (transport_pp _ _ _ _ @ _).
      refine ((ap _ (transportD_compose
                       (fun obj => obj -> obj -> Type)
                       (fun obj mor =>
                          forall s d d' : obj, mor d d' -> mor s d -> mor s d') object H'
                       (morphism C) (@compose C))^)
                @ (transport_apD_transportD
                     _
                     morphism
                     (fun x mor => forall s d d' : x, mor d d' -> mor s d -> mor s d') H'
                     (@compose C))).
    - refine (_ @ apD (@identity) H'); cbn.
      refine (transport_pp _ _ _ _ @ _).
      refine ((ap _ (transportD_compose
                       (fun obj => obj -> obj -> Type)
                       (fun obj mor =>
                          forall x : obj, mor x x) object H'
                       (morphism C) (@identity C))^)
                @ (transport_apD_transportD
                     _
                     morphism
                     (fun x mor => forall s : x, mor s s) H'
                     (@identity C))).
  Defined.

  (** ** Classify equality of precategorys up to equivalence *)
  Lemma equiv_path_precategory_uncurried'__eissect `{Funext} (C D : PreCategory)
  : forall x : path_precategory''_T C D,
      path_precategory_uncurried'_inv (path_precategory_uncurried' C D x) = x.
  Proof.
    destruct C, D; cbn in *.
    intros [H0' [H1' [H2' H3']]].
    path_induction.
    cbn.
    repeat (edestruct (center (_ = _)); try reflexivity).
  Qed.

  Lemma equiv_path_precategory_uncurried' `{Funext} (C D : PreCategory)
  : path_precategory''_T C D <~> C = D.
  Proof.
    apply (equiv_adjointify (@path_precategory_uncurried' _ C D)
                            (@path_precategory_uncurried'_inv C D)).
    - hnf.
      intros [].
      apply path_precategory_uncurried'_idpath.
    - hnf.
      apply equiv_path_precategory_uncurried'__eissect.
  Defined.

  Definition equiv_path_precategory_uncurried `{Funext} (C D : PreCategory)
  : path_precategory'_T C D <~> C = D
    := ((equiv_path_precategory_uncurried' C D)
          oE (BuildEquiv
                _ _ _
                (isequiv__path_precategory''_T__of__path_precategory'_T C D))).

  Definition path_precategory_uncurried `{Funext} C D : _ -> _
    := equiv_path_precategory_uncurried C D.

  (** ** Curried version of path classifying lemma *)
  Lemma path_precategory' `{fs : Funext} (C D : PreCategory)
  : forall (Hobj : object C = object D)
           (Hmor : transport (fun obj => obj -> obj -> Type)
                             Hobj
                             (morphism C)
                   = morphism D),
      transport _
                Hmor
                (transportD (fun obj => obj -> obj -> Type)
                            (fun obj mor => forall s d d', mor d d' -> mor s d -> mor s d')
                            Hobj
                            (morphism C)
                            (@compose C))
      = @compose D
      -> C = D.
  Proof.
    intros.
    apply path_precategory_uncurried.
    repeat esplit; eassumption.
  Defined.

  (** ** Curried version of path classifying lemma, using [forall] in place of equality of functions *)
  Lemma path_precategory `{fs : Funext} (C D : PreCategory)
  : forall (Hobj : object C = object D)
           (Hmor : forall s d,
                     morphism C (transport idmap Hobj^ s) (transport idmap Hobj^ d)
                     = morphism D s d),
      (forall s d d' m m',
         transport idmap (Hmor _ _)
                   (@compose C _ _ _
                             (transport idmap (Hmor _ _)^ m)
                             (transport idmap (Hmor _ _)^ m'))
         = @compose D s d d' m m')
      -> C = D.
  Proof.
    intros Hobj Hmor Hcomp.
    pose (path_forall
            _ _
            (fun s =>
               path_forall
                 _ _
                 (fun d =>
                    (ap10 (@transport_arrow Type idmap (fun x => x -> Type) _ _ Hobj (@morphism C) _) _)
                      @ (@transport_arrow Type idmap _ _ _ Hobj (@morphism C _) _)
                      @ (transport_const _ _)
                      @ Hmor s d)))
      as Hmor'.
    eapply (path_precategory' C D Hobj Hmor').
    repeat (apply path_forall; intro).
    refine (_ @ Hcomp _ _ _ _ _); clear Hcomp.
    subst Hmor'.
    cbn.
    abstract (
        destruct C, D;
        cbn in *;
          destruct Hobj;
        cbn in *;
          repeat match goal with
                   | _ => reflexivity
                   | _ => rewrite !concat_1p
                   | _ => rewrite !transport_forall_constant, !transport_arrow
                   | _ => progress transport_path_forall_hammer
                   | [ |- transport ?P ?p^ ?u = ?v ]
                     => (apply (@moveR_transport_V _ P _ _ p u v); progress transport_path_forall_hammer)
                   | [ |- ?u = transport ?P ?p^ ?v ]
                     => (apply (@moveL_transport_V _ P _ _ p u v); progress transport_path_forall_hammer)
                   | [ |- context[?H ?x ?y] ]
                     => (destruct (H x y); clear H)
                   | _ => progress f_ap
                 end
      ).
  Defined.
End path_category.

(** ** Tactic for proving equality of precategories *)
(** We move the funext inference outside the loop. *)
Ltac path_category :=
  idtac;
  let lem := constr:(@path_precategory _) in
  repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => simple refine (lem _ _ _ _ _); cbn
         end.
