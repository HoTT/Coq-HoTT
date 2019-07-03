(** * Coercions between hom-set adjunctions and unit+counit adjunctions *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions Adjoint.Dual Adjoint.Hom.
Require Import FunctorCategory.Core Category.Morphisms.
Require Import Category.Dual Functor.Dual.
Require Import Category.Prod.
Require Import HomFunctor NaturalTransformation.Isomorphisms.
Require Import Functor.Composition.Core.
Require Import FunctorCategory.Morphisms.
Require Import Functor.Identity.
Require Import SetCategory.Core SetCategory.Morphisms.
Require Import Basics.Trunc HProp HSet Types.Sigma HoTT.Tactics Equivalences TruncType.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

(** ** unit+UMP from hom-set adjunction *)
Section AdjunctionEquivalences.
  Context `{Funext}.
  Variables C D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Open Scope morphism_scope.

  (** We need to jump through some hoops with [simpl] for speed *)
  Section adjunction_naturality.
    Variable A : AdjunctionHom F G.

    Section nat1.
      Context c d d'
              (f : morphism D (F c) d)
              (g : morphism D d d').

      Let adjunction_naturalityT
        := Eval simpl in
            G _1 g o A (c, d) f = A (c, d') (g o f).

      Lemma adjunction_naturality : adjunction_naturalityT.
      Proof.
        pose proof (ap10 (commutes A (c, d) (c, d') (1%morphism, g))^ f) as H'; simpl in *.
        rewrite ?identity_of, ?left_identity, ?right_identity in H'.
        exact H'.
      Qed.
    End nat1.

    Section nat2.
      Context c c' d
              (f : morphism D (F c') d)
              (g : morphism C c c').

      Let adjunction_naturalityT'
        := Eval simpl in
            A (c', d) f o g = A (c, d) (f o F _1 g).

      Lemma adjunction_naturality' : adjunction_naturalityT'.
      Proof.
        pose proof (ap10 (commutes A (c', d) (c, d) (g, 1%morphism))^ f) as H'; simpl in *.
        rewrite ?identity_of, ?left_identity, ?right_identity in H'.
        exact H'.
      Qed.
    End nat2.
  End adjunction_naturality.

  (**
     Quoting from Awodey's "Category Theory":

     Proposition 9.4. Given categories and functors,

     [F : C ↔ D : G]

     the following conditions are equivalent:

     1. [F] is left adjoint to [G]; that is, there is a natural
        transformation

        [η : 1_C → G ∘ F]

        that has the UMP of the unit:

        For any [c : C], [d : D] and [f : c -> G d] there exists a
        unique [g : F c → d] such that [f = G g ∘ η c].

     2. For any [c : C] and [d : D] there is an isomorphism,

        [ϕ : Hom_D (F c, d) ≅ Hom_C (c, G d)]

        that is natural in both [c] and [d].

     Moreover, the two conditions are related by the formulas

     [ϕ g = G g ∘ η c]

     [η c = ϕ(1_{F c})]
     *)

  Lemma adjunction_unit__of__adjunction_hom_helper (A : AdjunctionHom F G)
        (c : C) (d : D) (f : morphism C c (G d))
  : IsHProp {g : morphism D (F c) d & G _1 g o A (c, F c) 1 = f}.
  Proof.
    apply hprop_allpath.
    intros [g0 H0] [g1 H1]; apply path_sigma_hprop; simpl.
    destruct H1.
    rewrite !adjunction_naturality in H0.
    rewrite !right_identity in H0.
    change (idmap g0 = idmap g1).
    rewrite <- (ap10 (@left_inverse _ _ _ (A (c, d)) _)).
    simpl rewrite H0.
    let k := constr:(ap10 (@left_inverse _ _ _ (A (c, d)) _)) in
    simpl rewrite k. (* https://coq.inria.fr/bugs/show_bug.cgi?id=3773 and https://coq.inria.fr/bugs/show_bug.cgi?id=3772 (probably) *)
    reflexivity.
  Qed.

  Lemma adjunction_unit__of__adjunction_hom__mate_of__commutes
        (A : AdjunctionHom F G) (s d : C) (m : morphism C s d)
  : A (d, F d) 1 o m = G _1 (F _1 m) o A (s, F s) 1.
  Proof.
    simpl; rewrite adjunction_naturality', adjunction_naturality.
    rewrite ?left_identity, ?right_identity.
    reflexivity.
  Qed.

  Definition adjunction_unit__of__adjunction_hom (A : AdjunctionHom F G)
  : AdjunctionUnit F G.
  Proof.
    exists (Build_NaturalTransformation
              1 (G o F)
              (fun c => A (c, F c) 1)
              (adjunction_unit__of__adjunction_hom__mate_of__commutes A)).
    simpl in *.
    intros c d f.
    apply contr_inhabited_hprop.
    - apply adjunction_unit__of__adjunction_hom_helper.
    - exact ((A (c, d))^-1%morphism f;
             ((adjunction_naturality A _ _ _ _ _)
                @ (ap (A (c, d)) (right_identity _ _ _ _))
                @ (ap10 (@right_inverse _ _ _ (A (c, d)) _) f))%path).
  Defined.
End AdjunctionEquivalences.

Section isequiv.
  (** We want to be able to use this without needing [Funext].  So, first, we prove that the types of hom-sets are equivalent. *)
  Variables C D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Open Scope morphism_scope.

  Variable T : AdjunctionUnit F G.

  Lemma equiv_hom_set_adjunction
        (c : C) (d : D)
  : morphism C c (G d) <~> morphism D (F c) d.
  Proof.
    refine (equiv_adjointify
              (fun f => (@center _ (T.2 _ _ f)).1)
              (fun g => G _1 g o T.1 c)
              _ _);
    intro.
    - match goal with
        | [ |- @pr1 ?A ?P ?x = ?y ]
          => change (x.1 = (existT P y idpath).1)
      end.
      apply (ap pr1).
      apply contr.
    - match goal with
        | [ |- context[?x.1] ]
          => apply x.2
      end.
  Defined.
End isequiv.

(** ** hom-set adjunction from unit+ump adjunction *)
Section AdjunctionEquivalences'.
  Context `{Funext}.
  Variables C D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Local Open Scope morphism_scope.

  Lemma adjunction_hom__of__adjunction_unit__commutes
        (T : AdjunctionUnit F G)
        sc sd dc dd
        (mc : morphism C dc sc) (md : morphism D sd dd)
  : (fun x : morphism D (F sc) sd => G _1 (md o x o F _1 mc) o T .1 dc) =
    (fun x : morphism D (F sc) sd => G _1 md o (G _1 x o T .1 sc) o mc).
  Proof.
    apply path_forall; intro.
    rewrite !composition_of, !associativity.
    simpl rewrite (commutes T.1).
    reflexivity.
  Qed.

  Definition adjunction_hom__of__adjunction_unit
             (T : AdjunctionUnit F G)
  : AdjunctionHom F G.
  Proof.
    constructor.
    (eexists (Build_NaturalTransformation _ _ _ _)).
    apply (@isisomorphism_natural_transformation _); simpl.
    exact (fun cd =>
             @isiso_isequiv
               _ _ _ _
               (equiv_isequiv
                  (equiv_hom_set_adjunction T (fst cd) (snd cd))^-1)).
    Grab Existential Variables.
    simpl.
    intros.
    exact (adjunction_hom__of__adjunction_unit__commutes T _ _ _ _ _ _).
  Defined.
End AdjunctionEquivalences'.

Definition AdjunctionUnitWithFunext `{Funext} C D F G := @AdjunctionUnit C D F G.
Definition AdjunctionCounitWithFunext `{Funext} C D F G := @AdjunctionCounit C D F G.
Definition AdjunctionUnitCounitWithFunext `{Funext} C D F G := @AdjunctionUnitCounit C D F G.
Identity Coercion AdjunctionUnit_Funext : AdjunctionUnitWithFunext >-> AdjunctionUnit.
Identity Coercion AdjunctionCounit_Funext : AdjunctionCounitWithFunext >-> AdjunctionCounit.
Identity Coercion AdjunctionUnitCounit_Funext : AdjunctionUnitCounitWithFunext >-> AdjunctionUnitCounit.

Definition adjunction_hom__of__adjunction_unit_Funext `{Funext} C D F G
           (A : AdjunctionUnitWithFunext _ _)
: AdjunctionHom _ _
  := @adjunction_hom__of__adjunction_unit _ C D F G A.
Definition AdjunctionHomOfAdjunctionCounit_Funext `{Funext} C D F G
           (A : AdjunctionCounitWithFunext _ _)
: AdjunctionHom _ _
  := @adjunction_hom__of__adjunction_unit _ C D F G (adjunction_unit_counit__of__adjunction_counit A).
Definition adjunction_hom__of__adjunction_unitCounit_Funext `{Funext} C D F G
           (A : AdjunctionUnitCounitWithFunext _ _)
: AdjunctionHom _ _
  := @adjunction_hom__of__adjunction_unit _ C D F G A.
