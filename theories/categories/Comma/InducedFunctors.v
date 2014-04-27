(** * Induced functors between comma categories *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual.
Require Import Category.Prod.
Require Import NaturalTransformation.Identity.
Require Import FunctorCategory.Core Cat.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import Comma.Core Comma.Projection.
Require Import types.Prod HoTT.Tactics types.Unit.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope category_scope.

(** ** Morphisms in [(A → C)ᵒᵖ × (B → C)] from [(s₀, s₁)] to [(d₀, d₁)] induce functors [(s₀ / s₁) → (d₀ / d₁)] *)
Section comma_category_induced_functor.
  Context `{Funext}.
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.

  Definition comma_category_induced_functor_object_of s d
             (m : morphism ((A -> C)^op * (B -> C)) s d)
             (x : fst s / snd s)
  : (fst d / snd d)
    := CommaCategory.Build_object
         (fst d) (snd d)
         (CommaCategory.a x)
         (CommaCategory.b x)
         ((snd m) (CommaCategory.b x) o CommaCategory.f x o (fst m) (CommaCategory.a x)).

  Lemma comma_category_induced_functor_object_of_identity s x
  : comma_category_induced_functor_object_of (Category.Core.identity s) x
    = x.
  Proof.
    let x1 := match goal with |- ?x1 = ?x2 => constr:(x1) end in
    let x2 := match goal with |- ?x1 = ?x2 => constr:(x2) end in
    apply (CommaCategory.path_object' x1 x2 idpath idpath).
    simpl.
    abstract (rewrite ?left_identity, ?right_identity; reflexivity).
  Defined.

  Definition comma_category_induced_functor_object_of_compose s d d'
             (m : morphism ((A -> C)^op * (B -> C)) d d')
             (m' : morphism ((A -> C)^op * (B -> C)) s d)
             x
  : comma_category_induced_functor_object_of (m o m') x
    = comma_category_induced_functor_object_of
        m
        (comma_category_induced_functor_object_of m' x).
  Proof.
    let x1 := match goal with |- ?x1 = ?x2 => constr:(x1) end in
    let x2 := match goal with |- ?x1 = ?x2 => constr:(x2) end in
    apply (CommaCategory.path_object' x1 x2 idpath idpath).
    abstract (
        destruct m', m, x;
        simpl in *;
          rewrite !associativity;
        reflexivity
      ).
  Defined.

  Definition comma_category_induced_functor_morphism_of s d m s0 d0
             (m0 : morphism (fst s / snd s) s0 d0)
  : morphism (fst d / snd d)
             (@comma_category_induced_functor_object_of s d m s0)
             (@comma_category_induced_functor_object_of s d m d0).
  Proof.
    simpl.
    let s := match goal with |- CommaCategory.morphism ?s ?d => constr:(s) end in
    let d := match goal with |- CommaCategory.morphism ?s ?d => constr:(d) end in
    refine (CommaCategory.Build_morphism s d (CommaCategory.g m0) (CommaCategory.h m0) _);
      simpl in *; clear.
    abstract (
        destruct_head prod;
        destruct_head CommaCategory.morphism;
        destruct_head CommaCategory.object;
        simpl in *;
          repeat (try_associativity_quick (rewrite <- !commutes || (progress f_ap)));
        repeat (try_associativity_quick (rewrite !commutes || (progress f_ap)));
        assumption
      ). (* 3.495 s *)
  Defined.

  Definition comma_category_induced_functor s d
             (m : morphism ((A -> C)^op * (B -> C)) s d)
  : Functor (fst s / snd s) (fst d / snd d).
  Proof.
    refine (Build_Functor (fst s / snd s) (fst d / snd d)
                          (@comma_category_induced_functor_object_of s d m)
                          (@comma_category_induced_functor_morphism_of s d m)
                          _
                          _
           );
    abstract (
        intros; apply CommaCategory.path_morphism; reflexivity
      ).
  Defined.
End comma_category_induced_functor.

(** ** Morphisms in [C] from [a] to [a'] induce functors [(C / a) → (C / a')] *)
Section slice_category_induced_functor.
  Context `{Funext}.
  Variable C : PreCategory.

  Section slice_coslice.
    Variable D : PreCategory.

    (** TODO(JasonGross): See if this can be recast as an exponential law functor about how [1 → Cat] is isomorphic to [Cat], or something *)
    Definition slice_category_induced_functor_nt s d (m : morphism D s d)
    : NaturalTransformation !s !d.
    Proof.
      exists (fun _ : Unit => m);
      simpl; intros; clear;
      abstract (autorewrite with category; reflexivity).
    Defined.

    Variable F : Functor C D.
    Variable a : D.

    Section slice.
      Definition slice_category_induced_functor F' a'
                 (m : morphism D a a')
                 (T : NaturalTransformation F' F)
      : Functor (F / a) (F' / a')
        := comma_category_induced_functor
             (s := (F, !a))
             (d := (F', !a'))
             (T, @slice_category_induced_functor_nt a a' m).

      Definition slice_category_nt_induced_functor F' T
        := @slice_category_induced_functor F' a 1 T.
      Definition slice_category_morphism_induced_functor a' m
        := @slice_category_induced_functor F a' m 1.
    End slice.

    Section coslice.
      Definition coslice_category_induced_functor F' a'
                 (m : morphism D a' a)
                 (T : NaturalTransformation F F')
      : Functor (a / F) (a' / F')
        := comma_category_induced_functor
             (s := (!a, F))
             (d := (!a', F'))
             (@slice_category_induced_functor_nt a' a m, T).

      Definition coslice_category_nt_induced_functor F' T
        := @coslice_category_induced_functor F' a 1 T.
      Definition coslice_category_morphism_induced_functor a' m
        := @coslice_category_induced_functor F a' m 1.
    End coslice.
  End slice_coslice.

  Definition slice_category_over_induced_functor a a' (m : morphism C a a')
  : Functor (C / a) (C / a')
    := Eval hnf in slice_category_morphism_induced_functor _ _ _ m.
  Definition coslice_category_over_induced_functor a a' (m : morphism C a' a)
  : Functor (a \ C) (a' \ C)
    := Eval hnf in coslice_category_morphism_induced_functor _ _ _ m.
End slice_category_induced_functor.

(** ** Functors [A → A'] functors [(cat / A) → (cat / A')] *)
Section cat_over_induced_functor.
  Context `{fs : Funext}.
  Variable P : PreCategory -> Type.
  Context `{H0 : forall C D, P C -> P D -> IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat fs P H0).

  Definition cat_over_induced_functor a a' (m : morphism cat a a')
  : Functor (cat / a) (cat / a')
    := slice_category_over_induced_functor cat a a' m.

  Definition over_cat_induced_functor a a' (m : morphism cat a' a)
  : Functor (a \ cat) (a' \ cat)
    := coslice_category_over_induced_functor cat a a' m.
End cat_over_induced_functor.
