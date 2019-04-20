(** This file defines [SetAlgebra], a specialized [Algebra] where
    the carriers are always sets. *)

Require Export HoTT.Classes.interfaces.ua_algebra.

Require Import HoTT.Basics.Equivalences.

Record SetAlgebra {σ : Signature} : Type := BuildSetAlgebra
  { algebra_setalgebra : Algebra σ
  ; is_hset_algebra_setalgebra : IsHSetAlgebra algebra_setalgebra }.

Arguments SetAlgebra : clear implicits.

Global Existing Instance is_hset_algebra_setalgebra.

Global Coercion algebra_setalgebra : SetAlgebra >-> Algebra.

(** To find a path [A = B] between set algebras [A B : SetAlgebra σ],
    it is enough to find a path between the defining algebras,
    [algebra_setalgebra A = algebra_setalgebra B]. *)

Lemma path_setalgebra `{Funext} {σ} (A B : SetAlgebra σ)
  (p : algebra_setalgebra A = algebra_setalgebra B)
  : A = B.
Proof.
  destruct A as [A AH], B as [B BH]. cbn in *.
  transparent assert (a : (p#AH = BH)) by apply path_ishprop.
  by path_induction.
Defined.

(** The id path is mapped to the id path by [path_setalgebra]. *)

Lemma path_setalgebra_1 `{Funext} {σ} (A : SetAlgebra σ)
  : path_setalgebra A A idpath = idpath.
Proof.
  transparent assert (p :
      (∀ I : IsHSetAlgebra A, path_ishprop I I = idpath)).
  - intros. apply path_ishprop.
  - unfold path_setalgebra. by rewrite p.
Qed.

(** The function [path_setalgebra A B] is an equivalence with inverse
    [ap algebra_setalgebra]. *)

Global Instance isequiv_path_setalgebra `{Funext} {σ : Signature}
  (A B : SetAlgebra σ)
  : IsEquiv (path_setalgebra A B).
Proof.
  refine (isequiv_adjointify
            (path_setalgebra A B) (ap algebra_setalgebra) _ _).
  - abstract (intro p; induction p; by rewrite path_setalgebra_1).
  - abstract (
      intro e; destruct A as [A AH], B as [B BH];
      cbn in e; destruct e;
      unfold path_setalgebra; by destruct path_ishprop).
Defined.
