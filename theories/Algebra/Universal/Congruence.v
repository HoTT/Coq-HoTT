(** This file implements algebra congruence relation. It serves as a
    universal algebra generalization of normal subgroup, ring ideal, etc.

    Congruence is used to construct quotients, in similarity with how
    normal subgroup and ring ideal is used to construct quotients. *)

Require Export HoTT.Algebra.Universal.Algebra.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HProp
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.Homomorphism.

Unset Elimination Schemes.

Import notations_algebra.

Section congruence.
  Context {σ : Signature} (A : Algebra σ) (Φ : forall s, Relation (A s)).

(** A finitary operation [f : A s1 * A s2 * ... * A sn -> A t]
    satisfies [OpCompatible f] iff

    <<
      Φ s1 x1 y1 * Φ s2 x2 y2 * ... * Φ sn xn yn
    >>

    implies

    <<
      Φ t (f (x1, x2, ..., xn)) (f (y1, y2, ..., yn)).
    >>

    The below definition generalizes this to infinitary operations.
*)

  Definition OpCompatible {w : SymbolType σ} (f : Operation A w) : Type
    := forall (a b : DomOperation A w),
       (forall i : Arity w, Φ (sorts_dom w i) (a i) (b i)) ->
       Φ (sort_cod w) (f a) (f b).

  Class OpsCompatible : Type
    := ops_compatible : forall (u : Symbol σ), OpCompatible u.#A.

  Global Instance trunc_ops_compatible `{Funext} {n : trunc_index}
    `{!forall s x y, IsTrunc n (Φ s x y)}
    : IsTrunc n OpsCompatible.
  Proof.
    apply trunc_forall.
  Defined.

  (** A family of relations [Φ] is a congruence iff it is a family of
      mere equivalence relations and [OpsCompatible A Φ] holds. *)

  Class IsCongruence : Type := Build_IsCongruence
   { is_mere_relation_cong : forall (s : Sort σ), is_mere_relation (A s) (Φ s)
   ; equiv_rel_cong : forall (s : Sort σ), EquivRel (Φ s)
   ; ops_compatible_cong : OpsCompatible }.

  Global Arguments Build_IsCongruence {is_mere_relation_cong}
                                      {equiv_rel_cong}
                                      {ops_compatible_cong}.

  Global Existing Instance is_mere_relation_cong.

  Global Existing Instance equiv_rel_cong.

  Global Existing Instance ops_compatible_cong.

  Global Instance hprop_is_congruence `{Funext} : IsHProp IsCongruence.
  Proof.
    apply (equiv_hprop_allpath _)^-1.
    intros [C1 C2 C3] [D1 D2 D3].
    by destruct (path_ishprop C1 D1),
                (path_ishprop C2 D2),
                (path_ishprop C3 D3).
  Defined.

End congruence.

(** A homomorphism [f : forall s, A s -> B s] is compatible
    with a congruence [Φ] iff [Φ s x y] implies [f s x = f s y]. *)

Definition HomCompatible {σ : Signature} {A B : Algebra σ}
  (Φ : forall s, Relation (A s)) `{!IsCongruence A Φ}
  (f : forall s, A s -> B s) `{!IsHomomorphism f}
  : Type
  := forall s (x y : A s), Φ s x y -> f s x = f s y.

