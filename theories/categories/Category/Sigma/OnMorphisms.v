Require Import HSet types.Unit HoTT.Tactics types.Forall types.Sigma HProp.
Require Import Category.Core Functor.Core Category.Sigma.Core.
Require Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths.
Import Functor.Identity.FunctorIdentityNotations.
Import Functor.Composition.Core.FunctorCompositionCoreNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation sigT_type := Coq.Init.Specif.sigT.
Local Notation projT1_type := Coq.Init.Specif.projT1.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section sigT_mor.
  Variable A : PreCategory.
  Variable Pmor : forall s d, morphism A s d -> Type.

  Local Notation mor s d := (sigT_type (Pmor s d)).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_Associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Definition sigT_mor : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (object A)
              (fun s d => mor s d)
              (fun x => identity x)
              (fun s d d' m1 m2 => compose m1 m2)
              _
              _
              _
              _);
    assumption.
  Defined.

  Definition pr1_mor : Functor sigT_mor A
    := Build_Functor
         sigT_mor A
         idmap
         (fun _ _ => @projT1_type _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition sigT_mor_as_sigT : PreCategory.
  Proof.
    refine (@sigT A (fun _ => Unit) (fun s d => @Pmor (projT1 s) (projT1 d)) _ (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2) _ _ _);
    intros; trivial.
  Defined.

  Definition sigT_functor_mor : Functor sigT_mor_as_sigT sigT_mor
    := Build_Functor
         sigT_mor_as_sigT sigT_mor
         (@projT1_type _ _)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition sigT_functor_mor_inv : Functor sigT_mor sigT_mor_as_sigT
    := Build_Functor
         sigT_mor sigT_mor_as_sigT
         (fun x => existT _ x tt)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Local Open Scope functor_scope.

  Lemma sigT_mor_eq `{Funext}
  : sigT_functor_mor o sigT_functor_mor_inv = 1
    /\ sigT_functor_mor_inv o sigT_functor_mor = 1.
  Proof.
    split; path_functor; simpl; trivial.
    refine (existT
              _
              (path_forall
                 _
                 _
                 (fun x
                  => match x with
                       | (_; tt) => _
                     end))
              _).
    instantiate (1 := idpath).
    repeat (apply path_forall; intro).
    destruct_head @sigT_type.
    destruct_head Unit.
    rewrite !transport_forall_constant.
    transport_path_forall_hammer.
    reflexivity.
  Qed.

  Definition sigT_mor_compat : pr1_mor o sigT_functor_mor = pr1
    := idpath.
End sigT_mor.

Arguments pr1_mor {A Pmor _ Pidentity Pcompose P_Associativity P_left_identity P_right_identity}.

Section sigT_mor_hProp.
  Variable A : PreCategory.
  Variable Pmor : forall s d, morphism A s d -> Type.

  Local Notation mor s d := (sigT_type (Pmor s d)).
  Context `(HPmor : forall s d m, IsHProp (Pmor s d m)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Local Ltac t ex_tac :=
    intros;
    simpl;
    apply path_sigma_uncurried;
    simpl;
    ex_tac;
    apply allpath_hprop.

  Let P_associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).
  Proof.
    abstract t ltac:(exists (associativity _ _ _ _ _ _ _ _))
      using P_associativity_on_morphisms_subproof.
  Defined.

  Let P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.
  Proof.
    clear P_associativity.
    abstract t ltac:(exists (left_identity _ _ _ _))
      using P_left_identity_on_morphisms_subproof.
  Defined.

  Let P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.
  Proof.
    clear P_associativity P_left_identity.
    abstract t ltac:(exists (right_identity _ _ _ _))
      using P_right_identity_on_morphisms_subproof.
  Defined.

  Definition sig_mor : PreCategory
    := Eval cbv delta [P_associativity P_left_identity P_right_identity]
      in @sigT_mor A Pmor _ Pidentity Pcompose P_associativity P_left_identity P_right_identity.

  Definition proj1_sig_mor : Functor sig_mor A
    := pr1_mor.
End sigT_mor_hProp.

Arguments proj1_sig_mor {A Pmor HPmor Pidentity Pcompose}.
