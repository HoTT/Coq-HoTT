Require Import
  HoTT.Basics.Equivalences
  HoTT.HProp
  HoTT.Types.Universe
  HoTT.Types.Forall
  HoTT.Classes.interfaces.canonical_names
  HoTT.Classes.interfaces.ua_algebra.

Import algebra_notations ne_list.notations.

Section congruence.
  Context {σ : Signature} (A : Algebra σ) (Φ : ∀ s, Relation (A s)).

(** An operation [f : A s1 → A s2 → ... → A sn → A t] satisfies
    [OpCompatible f] iff

    <<
      Φ s1 x1 y1 ∧ Φ s2 x2 y2 ∧ ... ∧ Φ sn xn yn
    >>

    implies

    <<
      Φ t (f x1 x2 ... xn) (f y1 y2 ... yn).
    >>
*)

  Definition OpCompatible {w : SymbolType σ} (f : Operation A w)
    : Type
    := ∀ (a b : FamilyProd A (dom_symboltype w)),
       for_all_2_family_prod A A Φ a b ->
       Φ (cod_symboltype w) (ap_operation f a) (ap_operation f b).

  Class OpsCompatible : Type
    := ops_compatible : ∀ (u : Symbol σ), OpCompatible u.#A.

  Global Instance trunc_ops_compatible `{Funext} {n : trunc_index}
    `{!∀ s x y, IsTrunc n (Φ s x y)}
    : IsTrunc n OpsCompatible.
  Proof.
    apply istrunc_forall.
  Qed.

  (** A family of relations [Φ] is a congruence iff it is a family of
      mere equivalence relations and [OpsCompatible A Φ] holds. *)

  Class IsCongruence : Type := BuildIsCongruence
   { is_mere_relation_cong : ∀ (s : Sort σ), is_mere_relation (A s) (Φ s)
   ; equiv_rel_cong : ∀ (s : Sort σ), EquivRel (Φ s)
   ; ops_compatible_cong : OpsCompatible }.

  Global Arguments BuildIsCongruence {is_mere_relation_cong}
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

(** If [Φ] is a congruence and [f : A s1 → A s2 → ... → A sn] an
    operation such that [OpCompatible A Φ f] holds.
    Then [OpCompatible (f x)] holds for all [x : A s1]. *)

Lemma op_compatible_cons {σ : Signature} {A : Algebra σ}
  (Φ : ∀ s, Relation (A s)) `{!IsCongruence A Φ}
  (s : Sort σ) (w : SymbolType σ) (f : Operation A (s ::: w))
  (x : A s) (P : OpCompatible A Φ f)
  : OpCompatible A Φ (f x).
Proof.
  intros a b R.
  exact (P (x,a) (x,b) (EquivRel_Reflexive x, R)).
Defined.
