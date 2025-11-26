From HoTT Require Import Basics Types Truncations.Core.
Require Import Pointed.Core.
Require Import WildCat.Core Homotopy.ExactSequence.
Require Import AbGroups.AbelianGroup AbSES.Core AbGroups.Biproduct.

Local Open Scope pointed_scope.
Local Open Scope type_scope.
Local Open Scope mc_add_scope.

(** * The direct sum of short exact sequences *)

(** Biproducts of abelian groups preserve exactness. *)
Lemma ab_biprod_exact {A E B X F Y : AbGroup}
      (i : A $-> E) (p : E $-> B) `{ex0 : IsExact (Tr (-1)) _ _ _ i p}
      (j : X $-> F) (q : F $-> Y) `{ex1 : IsExact (Tr (-1)) _ _ _ j q}
  : IsExact (Tr (-1)) (functor_ab_biprod i j)
            (functor_ab_biprod p q).
Proof.
  snapply Build_IsExact.
  - snapply phomotopy_homotopy_hset.
    1: exact _.
    intro x; apply path_prod; cbn.
    + apply ex0.
    + apply ex1.
  - intros [[e f] u]; cbn.
    rapply contr_inhabited_hprop.
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

(** For any short exact sequences [E], [E'], [F], [F'], and morphisms [f : E -> E'] and [g : F -> F'] there is a morphism [E + F -> E' + F']. *)
Lemma functor_abses_directsum `{Funext} {A A' B B' C C' D D' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} {F : AbSES D C} {F' : AbSES D' C'}
      (f : AbSESMorphism E E') (g : AbSESMorphism F F')
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum E' F').
Proof.
  snapply Build_AbSESMorphism.
  + exact (functor_ab_biprod (component1 f) (component1 g)).
  + exact (functor_ab_biprod (component2 f) (component2 g)).
  + exact (functor_ab_biprod (component3 f) (component3 g)).
  + intro x.
    apply path_prod; apply left_square.
  + intro x.
    apply path_prod; apply right_square.
Defined.

(** For any short exact sequence [E], there is a morphism [E -> abses_direct_sum E E], where each component is ab_diagonal. *)
Definition abses_diagonal `{Funext} {A B : AbGroup} (E : AbSES B A)
  : AbSESMorphism E (abses_direct_sum E E).
Proof.
  snapply Build_AbSESMorphism.
  1,2,3: exact ab_diagonal.
  all: reflexivity.
Defined.

(** For any short exact sequence [E], there is dually a morphism [abses_direct_sum E E -> E], with each component being the codiagonal. *)
Definition abses_codiagonal `{Funext} {A B : AbGroup} (E : AbSES B A)
  : AbSESMorphism (abses_direct_sum E E) E.
Proof.
  snapply Build_AbSESMorphism.
  1,2,3: exact ab_codiagonal.
  all: intro x; cbn; apply grp_homo_op.
Defined.

(** There is always a morphism [abses_direct_sum E F -> abses_direct_sum F E] of short exact sequences, for any [E : AbSES B A] and [F : AbSES B' A']. *)
Definition abses_swap_morphism `{Funext} {A A' B B' : AbGroup}
           (E : AbSES B A) (F : AbSES B' A')
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum F E).
Proof.
  snapply Build_AbSESMorphism.
  1,2,3: exact direct_sum_swap.
  all: reflexivity.
Defined.

(** For [E, F, G : AbSES B A], there is a morphism [(E + F) + G -> (G + F) + E] induced by the above map, where [+] denotes [abses_direct_sum]. *)
Lemma abses_twist_directsum `{Funext} {A B : AbGroup} (E F G : AbSES B A)
  : AbSESMorphism (abses_direct_sum (abses_direct_sum E F) G)
                  (abses_direct_sum (abses_direct_sum G F) E).
Proof.
  snapply Build_AbSESMorphism.
  1,2,3: exact ab_biprod_twist.
  all: reflexivity.
Defined.
