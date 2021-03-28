(** * ∑-categories on morphisms - a category with the same objects, but a ∑ type for morphisms *)
Require Import HSet Types.Unit HoTT.Tactics Types.Forall Types.Sigma Basics.Trunc.
Require Import Category.Core Functor.Core Category.Sigma.Core.
Require Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths.
Import Functor.Identity.FunctorIdentityNotations.
Import Functor.Composition.Core.FunctorCompositionCoreNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation sig_type := Overture.sig.
Local Notation pr1_type := Overture.pr1.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

Section sig_mor.
  Variable A : PreCategory.
  Variable Pmor : forall s d, morphism A s d -> Type.

  Local Notation mor s d := (sig_type (Pmor s d)).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  (** ** Definition of [sig_mor]-precategory *)
  Definition sig_mor' : PreCategory.
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

  (** ** First projection functor *)
  Definition pr1_mor : Functor sig_mor' A
    := Build_Functor
         sig_mor' A
         idmap
         (fun _ _ => @pr1_type _ _)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition sig_mor_as_sig : PreCategory.
  Proof.
    refine (@sig' A (fun _ => Unit) (fun s d => @Pmor (pr1_type s) (pr1_type d)) _ (fun _ => Pidentity _) (fun _ _ _ _ _ m1 m2 => Pcompose m1 m2) _ _ _);
    intros; trivial.
  Defined.

  Definition sig_functor_mor : Functor sig_mor_as_sig sig_mor'
    := Build_Functor
         sig_mor_as_sig sig_mor'
         (@pr1_type _ _)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Definition sig_functor_mor_inv : Functor sig_mor' sig_mor_as_sig
    := Build_Functor
         sig_mor' sig_mor_as_sig
         (fun x => exist _ x tt)
         (fun _ _ => idmap)
         (fun _ _ _ _ _ => idpath)
         (fun _ => idpath).

  Local Open Scope functor_scope.

  Lemma sig_mor_eq `{Funext}
  : sig_functor_mor o sig_functor_mor_inv = 1
    /\ sig_functor_mor_inv o sig_functor_mor = 1.
  Proof.
    split; path_functor; simpl; trivial.
    refine (exist
              _
              (path_forall
                 _
                 _
                 (fun x
                  => match x as x return (x.1; tt) = x with
                       | (_; tt) => idpath
                     end))
              _).
    repeat (apply path_forall; intro).
    destruct_head @sig_type.
    destruct_head Unit.
    rewrite !transport_forall_constant.
    transport_path_forall_hammer.
    reflexivity.
  Qed.

  Definition sig_mor_compat : pr1_mor o sig_functor_mor = pr1'
    := idpath.
End sig_mor.

Arguments pr1_mor {A Pmor _ Pidentity Pcompose P_associativity P_left_identity P_right_identity}.

Section sig_mor_hProp.
  Variable A : PreCategory.
  Variable Pmor : forall s d, morphism A s d -> Type.

  Local Notation mor s d := (sig_type (Pmor s d)).
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
    apply path_ishprop.

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

  (** ** Definition of [sig_mor]-precategory *)
  Definition sig_mor : PreCategory
    := Eval cbv delta [P_associativity P_left_identity P_right_identity]
      in @sig_mor' A Pmor _ Pidentity Pcompose P_associativity P_left_identity P_right_identity.

  (** ** First projection functor *)
  Definition proj1_sig_mor : Functor sig_mor A
    := pr1_mor.
End sig_mor_hProp.

Arguments proj1_sig_mor {A Pmor HPmor Pidentity Pcompose}.
