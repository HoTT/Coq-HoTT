(** * Functors about currying, between [C₁ × C₂ → D] and [C₁ → (C₂ → D)] *)
Require Import Category.Core Category.Prod FunctorCategory.Core Functor.Core NaturalTransformation.Core NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

Section law4.
  Context `{Funext}.
  Variables C1 C2 D : PreCategory.

  Local Open Scope morphism_scope.

  Local Ltac do_exponential4_helper rew_comp :=
    intros; simpl;
    repeat (simpl;
            match goal with
              | _ => reflexivity
              | _ => progress rew_comp
              | _ => rewrite !identity_of
              | _ => rewrite !left_identity
              | _ => rewrite !right_identity
              | _ => rewrite ?associativity; progress f_ap
              | _ => rewrite <- ?associativity; progress f_ap
              | _ => rewrite !commutes
              | _ => rewrite ?associativity, !commutes
              | _ => rewrite <- ?associativity, !commutes
            end).

  (** ** [(yⁿ)ᵐ → yⁿᵐ] *)
  Section functor.
    Local Ltac do_exponential4
      := do_exponential4_helper ltac:(rewrite !composition_of).

    Definition functor_object_of
    : (C1 -> (C2 -> D))%category -> (C1 * C2 -> D)%category.
    Proof.
      intro F; hnf in F |- *.
      refine (Build_Functor
                (C1 * C2) D
                (fun c1c2 => F (fst c1c2) (snd c1c2))
                (fun s d m => F (fst d) _1 (snd m) o (F _1 (fst m)) (snd s))
                _
                _);
        abstract do_exponential4.
    Defined.

    Definition functor_morphism_of
               s d (m : morphism (C1 -> (C2 -> D)) s d)
    : morphism (C1 * C2 -> D)
               (functor_object_of s)
               (functor_object_of d).
    Proof.
      simpl.
      refine (Build_NaturalTransformation
                (functor_object_of s)
                (functor_object_of d)
                (fun c => m (fst c) (snd c))
                _);
        abstract (
            repeat match goal with
                     | [ |- context[components_of ?T ?x o components_of ?U ?x] ] =>
                       change (T x o U x) with ((compose (C := (_ -> _)) T U) x)
                     | _ => f_ap
                     | _ => rewrite !commutes
                     | _ => do_exponential4
                   end
          ).
    Defined.

    Definition functor
    : Functor (C1 -> (C2 -> D)) (C1 * C2 -> D).
    Proof.
      refine (Build_Functor
                (C1 -> (C2 -> D)) (C1 * C2 -> D)
                functor_object_of
                functor_morphism_of
                _
                _);
      abstract by path_natural_transformation.
    Defined.
  End functor.

  (** ** [yⁿᵐ → (yⁿ)ᵐ] *)
  Section inverse.
    Local Ltac do_exponential4_inverse
      := do_exponential4_helper ltac:(rewrite <- !composition_of).

    Section object_of.
      Variable F : Functor (C1 * C2) D.

      Definition inverse_object_of_object_of
      : C1 -> (C2 -> D)%category.
      Proof.
        intro c1.
        refine (Build_Functor
                  C2 D
                  (fun c2 => F (c1, c2))
                  (fun s2 d2 m2 => F _1 ((identity c1, m2) : morphism (_ * _) (c1, s2) (c1, d2)))
                  _
                  _);
          abstract do_exponential4_inverse.
      Defined.

      Definition inverse_object_of_morphism_of
                 s d (m : morphism C1 s d)
      : morphism (C2 -> D)
                 (inverse_object_of_object_of s)
                 (inverse_object_of_object_of d).
      Proof.
        refine (Build_NaturalTransformation
                  (inverse_object_of_object_of s)
                  (inverse_object_of_object_of d)
                  (fun c => F _1 ((m, identity c) : morphism (_ * _) (s, c) (d, c)))
                  _);
        abstract do_exponential4_inverse.
      Defined.

      Definition inverse_object_of
      : (C1 -> (C2 -> D))%category.
      Proof.
        refine (Build_Functor
                  C1 (C2 -> D)
                  inverse_object_of_object_of
                  inverse_object_of_morphism_of
                  _
                  _);
        abstract (path_natural_transformation; do_exponential4_inverse).
      Defined.
    End object_of.

    Section morphism_of.
      Definition inverse_morphism_of_components_of
                 s d (m : morphism (C1 * C2 -> D) s d)
      : forall c, morphism (C2 -> D)
                           ((inverse_object_of s) c)
                           ((inverse_object_of d) c).
      Proof.
        intro c.
        refine (Build_NaturalTransformation
                  ((inverse_object_of s) c)
                  ((inverse_object_of d) c)
                  (fun c' => m (c, c'))
                  _).
        abstract do_exponential4_inverse.
      Defined.

      Definition inverse_morphism_of
                 s d (m : morphism (C1 * C2 -> D) s d)
      : morphism (C1 -> (C2 -> D))
                 (inverse_object_of s)
                 (inverse_object_of d).
      Proof.
        refine (Build_NaturalTransformation
                  (inverse_object_of s)
                  (inverse_object_of d)
                  (inverse_morphism_of_components_of m)
                  _).
        abstract (path_natural_transformation; do_exponential4_inverse).
      Defined.
    End morphism_of.

    Arguments inverse_morphism_of_components_of / _ _ _ _ .

    Definition inverse
    : Functor (C1 * C2 -> D) (C1 -> (C2 -> D)).
    Proof.
      refine (Build_Functor
                (C1 * C2 -> D) (C1 -> (C2 -> D))
                inverse_object_of
                inverse_morphism_of
                _
                _);
      abstract by path_natural_transformation.
    Defined.
  End inverse.
End law4.
