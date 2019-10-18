(** * Functoriality of the comma category construction *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import NaturalTransformation.Composition.Laws.
Require Import InitialTerminalCategory.
Require Import Functor.Paths.
Require Functor.Identity NaturalTransformation.Identity.
Require Import Category.Strict.
Require Comma.Core.
Local Set Warnings Append "-notation-overridden". (* work around bug #5567, https://coq.inria.fr/bugs/show_bug.cgi?id=5567, notation-overridden,parsing should not trigger for only printing notations *)
Import Comma.Core.
Local Set Warnings Append "notation-overridden".
Import Functor.Identity.FunctorIdentityNotations NaturalTransformation.Identity.NaturalTransformationIdentityNotations.
Require Import Trunc HoTT.Tactics PathGroupoids Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope morphism_scope.
Local Open Scope category_scope.

(** The comma category construction is functorial in its category
    arguments.  We really should be using ∏ (dependent product) here,
    but I'm lazy, and will instead expand it out. *)

Local Ltac helper_t fwd_tac bak_tac fin :=
  repeat
    first [ fin
          | rewrite <- ?Category.Core.associativity;
            progress repeat first [ bak_tac
                                  | apply ap10; apply ap ]
          | rewrite -> ?Category.Core.associativity;
            progress repeat first [ fwd_tac
                                  | apply ap ]
          | rewrite <- !composition_of ].

Local Tactic Notation "helper" tactic(fin) constr(hyp_fwd) constr(hyp_bak) :=
  let H := fresh in
  let H' := fresh in
  pose proof hyp_fwd as H;
    pose proof hyp_bak as H';
    simpl in *;
    helper_t ltac:(rewrite -> H) ltac:(rewrite <- H') fin.

Local Ltac functorial_helper_t unfold_lem :=
  repeat (apply path_forall || intro); simpl;
  rewrite !transport_forall_constant; simpl;
  transport_path_forall_hammer; simpl;
  apply CommaCategory.path_morphism; simpl;
  unfold unfold_lem; simpl;
  repeat match goal with
           | _ => exact idpath
           | [ |- context[CommaCategory.g (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @CommaCategory.g _ _ _ _ _ _ _) z)
           | [ |- context[CommaCategory.h (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @CommaCategory.h _ _ _ _ _ _ _) z)
           | [ |- context[transport (fun y => ?f (?g y) ?z)] ]
             => simpl rewrite (fun a b => @transport_compose _ _ a b (fun y => f y z) g)
           | [ |- context[transport (fun y => ?f (?g y))] ]
             => simpl rewrite (fun a b => @transport_compose _ _ a b (fun y => f y) g)
           | _ => rewrite !CommaCategory.ap_a_path_object'; simpl
           | _ => rewrite !CommaCategory.ap_b_path_object'; simpl
         end.

Section functorial.
  Section single_source.
    Variables A B C : PreCategory.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Section morphism_of.
      Variables A' B' C' : PreCategory.
      Variable S' : Functor A' C'.
      Variable T' : Functor B' C'.

      Variable AF : Functor A A'.
      Variable BF : Functor B B'.
      Variable CF : Functor C C'.

      Variable TA : NaturalTransformation (S' o AF) (CF o S).
      Variable TB : NaturalTransformation (CF o T) (T' o BF).

      Definition functorial_morphism_of_object_of : (S / T) -> (S' / T')
        := fun x => CommaCategory.Build_object
                      S' T'
                      (AF (CommaCategory.a x))
                      (BF (CommaCategory.b x))
                      (TB (CommaCategory.b x) o CF _1 (CommaCategory.f x) o TA (CommaCategory.a x)).

      Definition functorial_morphism_of_morphism_of
                 s d (m : morphism (S / T) s d)
      : morphism (S' / T') (functorial_morphism_of_object_of s) (functorial_morphism_of_object_of d).
      Proof.
        simpl in *.
        refine (CommaCategory.Build_morphism
                  (functorial_morphism_of_object_of s)
                  (functorial_morphism_of_object_of d)
                  (AF _1 (CommaCategory.g m))
                  (BF _1 (CommaCategory.h m))
                  _).
        unfold functorial_morphism_of_object_of; simpl.
        clear.
        abstract helper (exact (CommaCategory.p m)) (commutes TA) (commutes TB).
      Defined.

      Definition functorial_morphism_of : Functor (S / T) (S' / T').
      Proof.
        refine (Build_Functor
                  (S / T) (S' / T')
                  functorial_morphism_of_object_of
                  functorial_morphism_of_morphism_of
                  _
                  _);
        abstract (
            intros;
            apply CommaCategory.path_morphism; simpl;
            auto with functor
          ).
      Defined.
    End morphism_of.

    Section identity_of.
      Definition functorial_identity_of_helper x
      : @functorial_morphism_of_object_of _ _ _ S T 1 1 1 1 1 x = x.
      Proof.
        let A := match goal with |- ?A = ?B => constr:(A) end in
        let B := match goal with |- ?A = ?B => constr:(B) end in
        refine (@CommaCategory.path_object' _ _ _ _ _ A B 1%path 1%path _).
        exact (Category.Core.right_identity _ _ _ _ @ Category.Core.left_identity _ _ _ _)%path.
      Defined.

      Definition functorial_identity_of `{Funext}
      : @functorial_morphism_of
          _ _ _ S T
          1 1 1 1 1
        = 1%functor.
      Proof.
        path_functor; simpl.
        exists (path_forall _ _ functorial_identity_of_helper).
        simpl.
        functorial_helper_t functorial_identity_of_helper.
      Qed.
    End identity_of.
  End single_source.

  Section composition_of.
    Variables A B C : PreCategory.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Variables A' B' C' : PreCategory.
    Variable S' : Functor A' C'.
    Variable T' : Functor B' C'.

    Variables A'' B'' C'' : PreCategory.
    Variable S'' : Functor A'' C''.
    Variable T'' : Functor B'' C''.

    Variable AF : Functor A A'.
    Variable BF : Functor B B'.
    Variable CF : Functor C C'.

    Variable TA : NaturalTransformation (S' o AF) (CF o S).
    Variable TB : NaturalTransformation (CF o T) (T' o BF).

    Variable AF' : Functor A' A''.
    Variable BF' : Functor B' B''.
    Variable CF' : Functor C' C''.

    Variable TA' : NaturalTransformation (S'' o AF') (CF' o S').
    Variable TB' : NaturalTransformation (CF' o T') (T'' o BF').

    Let AF'' := (AF' o AF)%functor.
    Let BF'' := (BF' o BF)%functor.
    Let CF'' := (CF' o CF)%functor.

    Let TA'' : NaturalTransformation (S'' o AF'') (CF'' o S)
      := ((associator_2 _ _ _)
            o (CF' oL TA)
            o (associator_1 _ _ _)
            o (TA' oR AF)
            o associator_2 _ _ _)%natural_transformation.
    Let TB'' : NaturalTransformation (CF'' o T) (T'' o BF'')
      := ((associator_1 _ _ _)
            o (TB' oR BF)
            o (associator_2 _ _ _)
            o (CF' oL TB)
            o associator_1 _ _ _)%natural_transformation.

    Definition functorial_composition_of_helper x
    : (functorial_morphism_of TA' TB' o functorial_morphism_of TA TB)%functor x
      = functorial_morphism_of TA'' TB'' x.
    Proof.
      let A := match goal with |- ?A = ?B => constr:(A) end in
      let B := match goal with |- ?A = ?B => constr:(B) end in
      refine (@CommaCategory.path_object' _ _ _ _ _ A B 1%path 1%path _).
      subst AF'' BF'' CF'' TA'' TB''.
      simpl in *.
      abstract (
          autorewrite with morphism; simpl;
          helper (exact idpath) (commutes TA') (commutes TB')
        ).
    Defined.

    Definition functorial_composition_of `{Funext}
    : (functorial_morphism_of TA' TB' o functorial_morphism_of TA TB)%functor
      = functorial_morphism_of TA'' TB''.
    Proof.
      path_functor; simpl.
      exists (path_forall _ _ functorial_composition_of_helper).
      functorial_helper_t functorial_composition_of_helper.
    Qed.
  End composition_of.
End functorial.
