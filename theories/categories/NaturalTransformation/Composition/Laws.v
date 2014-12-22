(** * Laws about composition of functors *)
Require Import Category.Core Functor.Core Functor.Identity Functor.Composition.Core NaturalTransformation.Core NaturalTransformation.Identity NaturalTransformation.Composition.Core NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Section natural_transformation_identity.
  Context `{Funext}.

  Variables C D : PreCategory.

  (** ** left identity : [1 ∘ T = T] *)
  Lemma left_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : 1 o T = T.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  (** ** right identity : [T ∘ 1 = T] *)
  Lemma right_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : T o 1 = T.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  (** ** right whisker left identity : [1 ∘ᴿ F = 1] *)
  Definition whisker_r_left_identity E
             (G : Functor D E) (F : Functor C D)
  : identity G oR F = 1.
  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  (** ** left whisker right identity : [G ∘ᴸ 1 = 1] *)
  Definition whisker_l_right_identity E
             (G : Functor D E) (F : Functor C D)
  : G oL identity F = 1.
  Proof.
    path_natural_transformation; auto with functor.
  Qed.
End natural_transformation_identity.

Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : natural_transformation.

Section whisker.
  Context `{fs : Funext}.

  (** ** whisker exchange law : [(G' ∘ᴸ T) ∘ (T' ∘ᴿ F) = (T' ∘ᴿ F') ∘ (G ∘ᴸ T)] *)
  Section exch.
    Variables C D E : PreCategory.
    Variables G G' : Functor D E.
    Variables F F' : Functor C D.
    Variable T' : NaturalTransformation G G'.
    Variable T : NaturalTransformation F F'.

    Lemma exchange_whisker
    : (G' oL T) o (T' oR F) = (T' oR F') o (G oL T).
    Proof.
      path_natural_transformation; simpl.
      symmetry.
      apply NaturalTransformation.Core.commutes.
    Qed.
  End exch.

  Section whisker.
    Variables C D : PreCategory.
    Variables F G H : Functor C D.
    Variable T : NaturalTransformation G H.
    Variable T' : NaturalTransformation F G.

    (** ** left whisker composition : [F ∘ᴸ (T ∘ T') = (F ∘ᴸ T) ∘ (F ∘ᴸ T')] *)
    Lemma composition_of_whisker_l E (I : Functor D E)
    : I oL (T o T') = (I oL T) o (I oL T').
    Proof.
      path_natural_transformation; apply composition_of.
    Qed.

    (** ** right whisker composition : [(T ∘ T') ∘ᴿ F = (T ∘ᴿ F) ∘ (T' ∘ᴿ F)] *)
    Lemma composition_of_whisker_r B (I : Functor B C)
    : (T o T') oR I = (T oR I) o (T' oR I).
    Proof.
      path_natural_transformation; apply idpath.
    Qed.
  End whisker.
End whisker.

Section associativity.
  (** ** associators - natural transformations between [F ∘ (G ∘ H)] and [(F ∘ G) ∘ H] *)
  Section functors.
    Variables B C D E : PreCategory.
    Variable F : Functor D E.
    Variable G : Functor C D.
    Variable H : Functor B C.

    Local Notation F0 := ((F o G) o H)%functor.
    Local Notation F1 := (F o (G o H))%functor.

    Definition associator_1 : NaturalTransformation F0 F1
      := Eval simpl in
          generalized_identity F0 F1 idpath idpath.

    Definition associator_2 : NaturalTransformation F1 F0
      := Eval simpl in
          generalized_identity F1 F0 idpath idpath.
  End functors.

  (** ** associativity : [(T ∘ U) ∘ V = T ∘ (U ∘ V)] *)
  Section nt.
    Context `{fs : Funext}.

    Local Open Scope natural_transformation_scope.

    Definition associativity
               C D F G H I
               (V : @NaturalTransformation C D F G)
               (U : @NaturalTransformation C D G H)
               (T : @NaturalTransformation C D H I)
    : (T o U) o V = T o (U o V).
    Proof.
      path_natural_transformation.
      apply associativity.
    Qed.
  End nt.
End associativity.

Section functor_identity.
  Context `{Funext}.

  Variables C D : PreCategory.

  Local Ltac nt_id_t := split; path_natural_transformation;
                        autorewrite with morphism; reflexivity.

  (** ** left unitors : natural transformations between [1 ∘ F] and [F] *)
  Section left.
    Variable F : Functor D C.

    Definition left_identity_natural_transformation_1
    : NaturalTransformation (1 o F) F
      := Eval simpl in generalized_identity (1 o F) F idpath idpath.
    Definition left_identity_natural_transformation_2
    : NaturalTransformation F (1 o F)
      := Eval simpl in generalized_identity F (1 o F) idpath idpath.

    Theorem left_identity_isomorphism
    : left_identity_natural_transformation_1 o left_identity_natural_transformation_2 = 1
      /\ left_identity_natural_transformation_2 o left_identity_natural_transformation_1 = 1.
    Proof.
      nt_id_t.
    Qed.
  End left.

  (** ** right unitors : natural transformations between [F ∘ 1] and [F] *)
  Section right.
    Variable F : Functor C D.

    Definition right_identity_natural_transformation_1 : NaturalTransformation (F o 1) F
      := Eval simpl in generalized_identity (F o 1) F idpath idpath.
    Definition right_identity_natural_transformation_2 : NaturalTransformation F (F o 1)
      := Eval simpl in generalized_identity F (F o 1) idpath idpath.

    Theorem right_identity_isomorphism
    : right_identity_natural_transformation_1 o right_identity_natural_transformation_2 = 1
      /\ right_identity_natural_transformation_2 o right_identity_natural_transformation_1 = 1.
    Proof.
      nt_id_t.
    Qed.
  End right.
End functor_identity.

(** ** Tactics for inserting appropriate associators, whiskers, and unitors *)
Ltac nt_solve_associator' :=
  repeat match goal with
           | _ => exact (associator_1 _ _ _)
           | _ => exact (associator_2 _ _ _)
           | _ => exact (left_identity_natural_transformation_1 _)
           | _ => exact (left_identity_natural_transformation_2 _)
           | _ => exact (right_identity_natural_transformation_1 _)
           | _ => exact (right_identity_natural_transformation_2 _)
           | [ |- NaturalTransformation (?F o _) (?F o _) ] =>
             refine (whisker_l F _)
           | [ |- NaturalTransformation (_ o ?F) (_ o ?F) ] =>
             refine (whisker_r _ F)
         end.
Ltac nt_solve_associator :=
  repeat first [ progress nt_solve_associator'
               | refine (compose (associator_1 _ _ _) _); progress nt_solve_associator'
               | refine (compose _ (associator_1 _ _ _)); progress nt_solve_associator'
               | refine (compose (associator_2 _ _ _) _); progress nt_solve_associator'
               | refine (compose _ (associator_2 _ _ _)); progress nt_solve_associator' ].
