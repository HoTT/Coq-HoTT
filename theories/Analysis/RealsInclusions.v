(** * Inclusions of the Cauchy reals, the HoTT book reals and the Dedekind reals *)

From HoTT Require Import Basics Truncations.Core.
From HoTT.Universes Require Import HSet.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Colimits Require Import Quotient.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  interfaces.cauchy
  interfaces.round
  implementations.peano_naturals
  theory.rings
  theory.rationals
  orders.orders
  orders.rings
  orders.rationals.
From HoTT.Analysis Require Import
  MetricSpace CauchyCompleteness CauchyStructure CauchyReals DedekindReals HoTTBookReals.

(** The Cauchy reals embed into the HoTT book reals, which embed into every Cauchy complete Archimedean ordered field, in particular into the Dedekind reals. *)

(** ** The Cauchy reals in the HoTT book reals *)

Section cauchy_reals.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
  Context (R : CauchyStructure Q) `{!IsHoTTBookReals Q R}.
  Local Notation close := (cs_close Q R).
  Local Notation rat := (cs_rat Q R).
  Local Notation lim := (cs_lim Q R).

  (** A rational sequence with a modulus gives a Cauchy approximation in [R]. *)
  Definition cauchy_sequence_approximation (s : CauchySequence Q)
    : CauchyApproximation Q close.
  Proof.
    snapply (Build_CauchyApproximation Q close (fun e => rat (s (cauchy_modulus Q s e)))).
    intros d e; apply cs_close_rat_rat.
    set (n := nat_max (cauchy_modulus Q s d) (cauchy_modulus Q s e)).
    apply (rational_close_triangle Q _ _ _ (s n)).
    - exact (cauchy_ismodulus Q s d _ _ (leq_refl _) (le_nat_max_l _ _)).
    - exact (cauchy_ismodulus Q s e _ _ (le_nat_max_r _ _) (leq_refl _)).
  Defined.

  Lemma qpos_plus_half (a : Qpos Q) : (a + a) / 2 = a.
  Proof.
    assert (p : a + a = 2 * a).
    { apply pos_eq; change (' a + ' a = (1 + 1) * ' a).
      rewrite plus_mult_distr_r, mult_1_l; reflexivity. }
    rewrite p; apply pos_unconjugate.
  Qed.

  (** Related sequences have the same limit in [R]. *)
  Lemma cauchy_sequence_lim_related (s t : CauchySequence Q) (r : cauchy_related Q s t)
    : lim (cauchy_sequence_approximation s) = lim (cauchy_sequence_approximation t).
  Proof.
    apply (cs_eq Q R); intro e.
    assert (p : e = (e / 3 + e / 3) + (e / 3 + e / 3) / 4 + (e / 3 + e / 3) / 4).
    { rewrite <- Qpos_plus_assoc, (qpos_quarter Q), qpos_plus_half.
      exact (pos_split3 e). }
    rewrite p; apply cs_close_lim_lim, cs_close_rat_rat, r.
  Qed.

  Definition cauchy_reals_to_hottbookreals `{Funext} : CauchyReals Q -> R
    := Quotient_rec (cauchy_related Q) R (fun s => lim (cauchy_sequence_approximation s))
         cauchy_sequence_lim_related.

  (** In a Cauchy complete Archimedean ordered field [F], the inclusion of the Cauchy reals into [R] commutes with the maps into [F]. Since the Cauchy reals embed into [F], they embed into [R]. *)

  Section field.
    Context {F : Type} `{OrderedField F} {Farch : ArchimedeanProperty Q F}
      `{!RoundUpStrict Q} `{!IsComplete Q F}.
    Let qinc : Cast Q F := rationals_to_field Q F.
    Existing Instance qinc.

    Lemma hottbookreals_to_field_cauchy_reals `{Funext} (x : CauchyReals Q)
      : hottbookreals_to_field Q R (F:=F) (cauchy_reals_to_hottbookreals x)
        = cauchy_reals_to_field Q F x.
    Proof.
      revert x; srapply Quotient_ind_hprop; intro s.
      change (hottbookreals_to_field Q R (lim (cauchy_sequence_approximation s))
              = cauchy_limit Q F s).
      rewrite (cshom_lim Q _ _ _).
      apply (field_close_eq Q); intro e.
      rewrite (pos_split3 e).
      apply field_close_symmetric.
      apply (field_close_le_triangle Q (e / 3 + e / 3) (e / 3) _
               (' s (cauchy_modulus Q s (e / 3)))).
      1: exact (cauchy_limit_close Q F s (e / 3)).
      set (y := map_cauchy_approximation Q _ _ (cauchy_sequence_approximation s)).
      assert (p : y (e / 3) = ' s (cauchy_modulus Q s (e / 3)))
        by exact (cshom_rat Q _ _ _ _).
      rewrite <- p.
      exact (isapproximationlimit_le Q y _ (isapproximationlimit_field_lim Q y) _).
    Qed.

    Lemma isinj_cauchy_reals_to_field `{Funext} : IsInjective (cauchy_reals_to_field Q F).
    Proof.
      intros x y; revert x; srapply Quotient_ind_hprop; intro s.
      revert y; srapply Quotient_ind_hprop; intros t p.
      apply qglue; intro e.
      apply (rational_close_field_close Q (F:=F)).
      assert (c := field_close_triangle Q _ _ _ _ _
                     (field_close_symmetric Q _ _ _ (cauchy_limit_close Q F s (e / 4)))
                     (transport (fun z => field_close Q _ z _) p^
                        (cauchy_limit_close Q F t (e / 4)))).
      rewrite (qpos_quarter Q), <- pos_split2 in c.
      exact c.
    Qed.

    Lemma isinj_cauchy_reals_to_hottbookreals `{Funext}
      : IsInjective cauchy_reals_to_hottbookreals.
    Proof.
      intros x y p; apply isinj_cauchy_reals_to_field.
      rewrite <- 2 hottbookreals_to_field_cauchy_reals, p; reflexivity.
    Qed.

    Definition isembedding_cauchy_reals_to_hottbookreals `{Funext}
      : IsEmbedding cauchy_reals_to_hottbookreals
      := isembedding_isinj_hset _ isinj_cauchy_reals_to_hottbookreals.

  End field.

End cauchy_reals.

(** ** The HoTT book reals in the Dedekind reals *)

(** The Archimedean property depends on a proof that the field has characteristic [0], which is a proposition. The instance for the Dedekind reals uses a different proof than the one derived from their ordered field structure, so we transport it. *)
Definition archimedean_property_change_char `{Funext} (Q : Type) `{Rationals Q}
  (F : Type) `{OrderedField F} (c c' : FieldCharacteristic F 0)
  : ArchimedeanProperty Q F (Achar:=c) -> ArchimedeanProperty Q F (Achar:=c').
Proof.
  assert (p : c = c').
  { snapply path_ishprop; unfold FieldCharacteristic; exact _. }
  destruct p; exact idmap.
Defined.

Section dedekind.
  Context `{Funext} `{Univalence}.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qroundup : RoundUpStrict@{_ UQ _ UQ} Q}.
  Local Notation RD := (DedekindReals Q (Qlt:=Qlt)).

  Definition hottbookreals_to_dedekind (R : CauchyStructure Q) `{!IsHoTTBookReals Q R}
    := hottbookreals_to_field Q R (F:=RD)
         (Farch:=archimedean_property_change_char Q RD _ _ (archimedean_dedekindreals Q)).

  #[export] Instance isembedding_hottbookreals_to_dedekind (R : CauchyStructure Q)
    `{!IsHoTTBookReals Q R}
    : IsEmbedding (hottbookreals_to_dedekind R)
    := isembedding_hottbookreals_to_field Q R (F:=RD)
         (Farch:=archimedean_property_change_char Q RD _ _ (archimedean_dedekindreals Q)).

  Definition cauchycomplete_hottbookreals_dedekind (R : CauchyStructure Q)
    `{!IsHoTTBookReals Q R}
    : CauchyComplete Q (cs_close Q R)
    := cauchycomplete_hottbookreals Q R (F:=RD)
         (Farch:=archimedean_property_change_char Q RD _ _ (archimedean_dedekindreals Q)).

  Definition isembedding_cauchy_reals_to_hottbookreals_dedekind (R : CauchyStructure Q)
    `{!IsHoTTBookReals Q R}
    : IsEmbedding (cauchy_reals_to_hottbookreals Q R)
    := isembedding_cauchy_reals_to_hottbookreals Q R (F:=RD)
         (Farch:=archimedean_property_change_char Q RD _ _ (archimedean_dedekindreals Q)).

End dedekind.
