(** * Cauchy reals *)

(** The Cauchy reals are the rational sequences equipped with a modulus of Cauchy convergence, quotiented by the relation identifying two such sequences when their terms at the moduli are close. In a Cauchy complete Archimedean ordered field, sending a sequence to its limit gives a canonical map from the Cauchy reals. *)

From HoTT Require Import Basics Truncations.Core.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Colimits Require Import Quotient.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  interfaces.cauchy
  implementations.peano_naturals
  theory.rings
  theory.dec_fields
  theory.rationals
  orders.orders
  orders.rings
  orders.rationals.
From HoTT_Contrib.Analysis Require Import MetricSpace CauchyCompleteness.

Section cauchy_reals.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.

  (** ** The Cauchy reals *)

  (** A rational sequence equipped with a modulus of Cauchy convergence. *)
  Record CauchySequence := {
    cauchy_seq :> nat -> Q;
    cauchy_modulus : Qpos Q -> nat;
    cauchy_ismodulus : MetricCauchyModulus Q (rational_close Q) cauchy_seq cauchy_modulus
  }.

  (** Two sequences are related when, for every [e], their terms at the moduli for [e / 4] are [e]-close. *)
  Definition cauchy_related (x y : CauchySequence) :=
    forall e : Qpos Q,
      rational_close Q e (x (cauchy_modulus x (e / 4))) (y (cauchy_modulus y (e / 4))).

  (** The Cauchy reals. *)
  Definition CauchyReals := Quotient cauchy_related.

  (** The inclusion of the rationals, as constant sequences. *)
  Definition const_cauchy_sequence (q : Q) : CauchySequence
    := {| cauchy_seq := fun _ => q; cauchy_modulus := fun _ => 0%nat;
          cauchy_ismodulus := fun e _ _ _ _ => rational_close_refl Q e q |}.

  Definition rationals_to_cauchy_reals (q : Q) : CauchyReals
    := class_of _ (const_cauchy_sequence q).

  (** ** The canonical map to a Cauchy complete field *)

  (** Two quarters make a half. *)
  Lemma qpos_quarter (e : Qpos Q) : e / 4 + e / 4 = e / 2.
  Proof.
    assert (p : e / 4 = e / 2 / 2).
    { apply pos_eq.
      change (' e * / (1 + (1 + (1 + 1))) = ' e * / (1 + 1) * / (1 + 1)).
      rewrite <- mult_assoc, <- dec_recip_distr.
      apply ap, ap.
      rewrite plus_mult_distr_l, mult_1_r, plus_assoc. reflexivity. }
    rewrite p. exact (pos_split2 (e / 2))^.
  Qed.

  Section limit.
    Context (F : Type) `{OrderedField F} {Farch : ArchimedeanProperty Q F}
      {Fcomplete : IsComplete Q F}.
    Let qinc : Cast Q F := rationals_to_field Q F.
    Existing Instance qinc.

    #[export] Instance cauchymodulus_cauchy_sequence (x : CauchySequence)
      : CauchyModulus Q F (fun n => ' x n) (cauchy_modulus x)
      := fun e m n lem len => field_close_rationals Q e _ _ (cauchy_ismodulus x e m n lem len).

    (** The limit of a rational sequence with a modulus. *)
    Definition cauchy_limit (x : CauchySequence) : F
      := (is_complete Q F _ _ (cauchymodulus_cauchy_sequence x)).1.

    Definition islimit_cauchy_limit (x : CauchySequence)
      : IsLimit Q F (fun n => ' x n) (cauchy_limit x)
      := (is_complete Q F _ _ (cauchymodulus_cauchy_sequence x)).2.

    (** The limit is [d + d]-close to the term at the modulus for [d]. *)
    Lemma cauchy_limit_close (x : CauchySequence) (d : Qpos Q)
      : field_close Q (d + d) (cauchy_limit x) (' x (cauchy_modulus x d)).
    Proof.
      assert (c := islimit_cauchy_limit x d). strip_truncations.
      destruct c as [N close].
      set (n := Nat.Core.nat_max N (cauchy_modulus x d)).
      apply (field_close_triangle Q _ _ _ (' x n)).
      - exact (close n (le_nat_max_l _ _)).
      - exact (cauchymodulus_cauchy_sequence x d n _ (le_nat_max_r _ _) (Nat.Core.leq_refl _)).
    Qed.

    (** Related sequences have the same limit. *)
    Lemma cauchy_limit_related (x y : CauchySequence) (r : cauchy_related x y)
      : cauchy_limit x = cauchy_limit y.
    Proof.
      apply (field_close_eq Q). intro e.
      assert (p : e = e / 2 / 4 + e / 2 / 4 + e / 2 + (e / 2 / 4 + e / 2 / 4)).
      { rewrite qpos_quarter, (qpos_plus_comm (e / 2 / 2) (e / 2)), <- Qpos_plus_assoc.
        rewrite <- (pos_split2 (e / 2)). exact (pos_split2 e). }
      rewrite p.
      apply (field_close_triangle Q _ _ _ (' y (cauchy_modulus y (e / 2 / 4)))).
      1: apply (field_close_triangle Q _ _ _ (' x (cauchy_modulus x (e / 2 / 4)))).
      - apply cauchy_limit_close.
      - apply (field_close_rationals Q), r.
      - apply field_close_symmetric, cauchy_limit_close.
    Qed.

    (** Hence sending a sequence to its limit gives a map from the Cauchy reals. *)
    Definition cauchy_reals_to_field : CauchyReals -> F
      := Quotient_rec cauchy_related F cauchy_limit cauchy_limit_related.

    (** It commutes with the inclusions of the rationals. *)
    Lemma cauchy_reals_to_field_rationals (q : Q)
      : cauchy_reals_to_field (rationals_to_cauchy_reals q) = ' q.
    Proof.
      apply (limit_unique Q (fun _ => ' q)).
      - exact (islimit_cauchy_limit (const_cauchy_sequence q)).
      - intro e. apply tr; exists 0%nat. intros n _.
        assert (epos := pos_rationals_to_field_qpos Q (F:=F) e).
        unfold field_close; rewrite plus_negate_r. split.
        + apply flip_pos_negate, epos.
        + exact epos.
    Qed.

    (** ** Cauchy reals in a Cauchy complete field *)

    (** An element of [F] is a Cauchy real when it is merely in the image of the Cauchy reals. *)
    Definition IsCauchyReal (x : F) := hexists (fun r => cauchy_reals_to_field r = x).

    (** Equivalently, it is merely the limit of a rational sequence with a modulus. *)
    Lemma iscauchyreal_iff_limit `{Funext} (x : F)
      : IsCauchyReal x <-> hexists (fun s : CauchySequence => IsLimit Q F (fun n => ' s n) x).
    Proof.
      split.
      - apply Trunc_rec. intros [r p]; revert r p.
        srapply (Quotient_ind_hprop cauchy_related). intros s p; apply tr.
        exists s. exact (transport _ p (islimit_cauchy_limit s)).
      - apply Trunc_functor. intros [s islim].
        exists (class_of _ s).
        exact (limit_unique Q _ _ _ (islimit_cauchy_limit s) islim).
    Qed.
  End limit.

End cauchy_reals.
