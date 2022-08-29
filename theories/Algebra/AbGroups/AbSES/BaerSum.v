Require Import Basics Types Pointed.
Require Import WildCat WildCat.Profunctor Homotopy.ExactSequence.
Require Import AbGroups.AbelianGroup AbSES.Core AbSES.Pullback AbSES.Pushout.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** ** The Baer sum of short exact sequences *)

(** Biproducts preserve exactness. *)
Lemma ab_biprod_exact {A E B X F Y : AbGroup}
      (i : A $-> E) (p : E $-> B) `{ex0 : IsExact (Tr (-1)) _ _ _ i p}
      (j : X $-> F) (q : F $-> Y) `{ex1 : IsExact (Tr (-1)) _ _ _ j q}
  : IsExact (Tr (-1)) (functor_ab_biprod i j)
            (functor_ab_biprod p q).
Proof.
  snrapply Build_IsExact.
  - snrapply phomotopy_homotopy_hset.
    1: exact _.
    intro x; apply path_prod; cbn.
    + apply ex0.
    + apply ex1.
  - intros [ef u]; cbn.
    rapply contr_inhabited_hprop.
    destruct ef as [e f].
    pose (U := (equiv_path_prod _ _)^-1 u); cbn in U.
    pose proof (a := isexact_preimage _ i p e (fst U)).
    pose proof (x := isexact_preimage _ j q f (snd U)).
    strip_truncations; apply tr.
    exists (ab_biprod_inl a.1 + ab_biprod_inr x.1); cbn.
    pose (IS := sg_set (ab_biprod B Y)). (* This hint speeds up the next line. *)
    apply path_sigma_hprop; cbn.
    apply path_prod; cbn.
    + rewrite right_identity.
      exact a.2.
    + rewrite left_identity.
      exact x.2.
Defined.

(** The pointwise direct sum of two short exact sequences. *)
Definition abses_direct_sum `{Funext} {B A B' A' : AbGroup} (E : AbSES B A) (F : AbSES B' A')
  : AbSES (ab_biprod B B') (ab_biprod A A')
  := Build_AbSES (ab_biprod E F)
                 (functor_ab_biprod (inclusion E) (inclusion F))
                 (functor_ab_biprod (projection E) (projection F))
                 (functor_ab_biprod_embedding _ _)
                 (functor_ab_biprod_surjection _ _)
                 (ab_biprod_exact _ _ _ _).

(** The Baer sum of two short exact sequences is obtained from the pointwise direct sum by pushing forth along the codiagonal and then pulling back along the diagonal. (Swapping the order of pushing forth and pulling back produces an isomorphic short exact sequence.) *)
Definition abses_baer_sum `{Univalence} {B A : AbGroup} (E F : AbSES B A)
  : AbSES B A
  := abses_pullback ab_diagonal (abses_pushout ab_codiagonal (abses_direct_sum E F)).


(** ** [AbSES'] is a profunctor *)

(** Given a morphism [f] of short exact sequences, the pushout of the domain along [f_1] equals the pullback of the codomain along [f_3]. *)
Lemma abses_pushout_is_pullback' `{Univalence} {A A' B B' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} (f : AbSESMorphism E E')
  : abses_pushout (component1 f) E $== abses_pullback (component3 f) E'.
Proof.
  (* The morphism [f : E -> E'] factors as [E -> f_1 E -> E'], where the first map is the map defining the pushout [f_1 E] and the second map is denoted [abses_pushout_morphism_rec f] below.  This second map is the identity on the first component, so it presents its domain as the pullback of [E'] along [f_3]. *)
  exact (abses_pullback_component1_id' (abses_pushout_morphism_rec f) (fun _ => idpath)).
Defined.

(** Given a morphism [f] of short exact sequences, the pushout of the domain along [f_1] equals the pullback of the codomain along [f_3]. *)
Definition abses_pushout_is_pullback `{Univalence} {A A' B B' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} (f : AbSESMorphism E E')
  : abses_pushout (component1 f) E = abses_pullback (component3 f) E'
  := equiv_path_abses_iso (abses_pushout_is_pullback' f).

Definition abses_pushout_pullback_reorder' `{Univalence} {A A' B B' : AbGroup}
  (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout f (abses_pullback g E) $== abses_pullback g (abses_pushout f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout. We define [F : Eg -> fE] to be the composite. Its first and third components are [f o id] and [id o g]. *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).
  (* We change [F] to a morphism that is the same except that the first and third components are [f] and [g]. Then [abses_pushout_is_pullback] shows that the pushout of [Eg] along [f] is equal to the pullback of [fE] along [g]. *)
  refine (abses_pushout_is_pullback' (Build_AbSESMorphism f (component2 F) g _ _)); apply F.
Defined.

(** This is the statement that [AbSES'] is a profunctor, but we state it separately because Coq is slow to unify [IsProfunctor AbSES'] against goals written in this foal. *)
Definition abses_pushout_pullback_reorder `{Univalence} {A A' B B' : AbGroup}
  (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout f (abses_pullback g E) = abses_pullback g (abses_pushout f E).
Proof.
  apply equiv_path_abses_iso.
  apply abses_pushout_pullback_reorder'.
Defined.

Global Instance isprofunctor_abses' `{Univalence}
  : IsProfunctor AbSES'.
Proof.
  intros ? ? g ? ? f E; cbn.
  apply abses_pushout_pullback_reorder.
Defined.
