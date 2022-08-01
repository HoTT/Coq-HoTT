Require Import Basics Types Pointed.
Require Import WildCat Homotopy.ExactSequence.
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
  - snrapply Build_pHomotopy.
    + intro x; apply path_prod; cbn.
      * apply ex0.
      * apply ex1.
    + apply path_ishprop.
  - intros [ef u]; cbn.
    rapply contr_inhabited_hprop.
    destruct ef as [e f].
    pose (U := (equiv_path_prod _ _)^-1 u); cbn in U.
    pose proof (a := isexact_preimage _ i p e (fst U)).
    pose proof (x := isexact_preimage _ j q f (snd U)).
    strip_truncations; apply tr.
    exists (ab_biprod_inl a.1 + ab_biprod_inr x.1); cbn.
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
