(** * Inclusions of the Cauchy reals, the HoTT book reals and the Dedekind reals *)

From HoTT Require Import Basics Types.Sigma Truncations.Core.
From HoTT.Universes Require Import HSet HProp.
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
From HoTT_Contrib.Analysis Require Import
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
Definition archimedean_property_change_char `{Funext} (Q : Type) `{RationalsToField Q}
  (F : Type) `{OrderedField F} (c c' : FieldCharacteristic F 0)
  : ArchimedeanProperty Q F (Achar:=c) -> ArchimedeanProperty Q F (Achar:=c').
Proof.
  assert (p : c = c').
  { snapply path_ishprop; unfold FieldCharacteristic; exact _. }
  destruct p; exact idmap.
Defined.

(** The following are stated outside a section, with all assumptions as arguments: applying them to the Dedekind reals constrains the universes of the rationals, and constraints on section universes cannot be added by later definitions. *)
Definition hottbookreals_to_dedekind `{Funext} `{Univalence} (Q : Type) {Qap : Apart Q} {Qplus : Plus Q}
  {Qmult : Mult Q} {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
  {Qle : Le Q} {Qlt : Lt Q} {QtoField : RationalsToField Q} {Qrats : Rationals Q}
  {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q} {Qroundup : RoundUpStrict Q}
  (R : CauchyStructure Q) `{!IsHoTTBookReals Q R}
  := hottbookreals_to_field Q R (F:=DedekindReals Q (Qlt:=Qlt))
       (Farch:=archimedean_property_change_char Q _ _ _ (archimedean_dedekindreals Q)).

#[export] Instance isembedding_hottbookreals_to_dedekind `{Funext} `{Univalence} (Q : Type) {Qap : Apart Q} {Qplus : Plus Q}
  {Qmult : Mult Q} {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
  {Qle : Le Q} {Qlt : Lt Q} {QtoField : RationalsToField Q} {Qrats : Rationals Q}
  {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q} {Qroundup : RoundUpStrict Q}
  (R : CauchyStructure Q) `{!IsHoTTBookReals Q R}
  : IsEmbedding (hottbookreals_to_dedekind Q R)
  := isembedding_hottbookreals_to_field Q R (F:=DedekindReals Q (Qlt:=Qlt))
       (Farch:=archimedean_property_change_char Q _ _ _ (archimedean_dedekindreals Q)).

Definition cauchycomplete_hottbookreals_dedekind `{Funext} `{Univalence} (Q : Type) {Qap : Apart Q} {Qplus : Plus Q}
  {Qmult : Mult Q} {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
  {Qle : Le Q} {Qlt : Lt Q} {QtoField : RationalsToField Q} {Qrats : Rationals Q}
  {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q} {Qroundup : RoundUpStrict Q}
  (R : CauchyStructure Q) `{!IsHoTTBookReals Q R}
  : CauchyComplete Q (cs_close Q R)
  := cauchycomplete_hottbookreals Q R (F:=DedekindReals Q (Qlt:=Qlt))
       (Farch:=archimedean_property_change_char Q _ _ _ (archimedean_dedekindreals Q)).

Definition isembedding_cauchy_reals_to_hottbookreals_dedekind `{Funext} `{Univalence} (Q : Type) {Qap : Apart Q} {Qplus : Plus Q}
  {Qmult : Mult Q} {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
  {Qle : Le Q} {Qlt : Lt Q} {QtoField : RationalsToField Q} {Qrats : Rationals Q}
  {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q} {Qroundup : RoundUpStrict Q}
  (R : CauchyStructure Q) `{!IsHoTTBookReals Q R}
  : IsEmbedding (cauchy_reals_to_hottbookreals Q R)
  := isembedding_cauchy_reals_to_hottbookreals Q R (F:=DedekindReals Q (Qlt:=Qlt))
       (Farch:=archimedean_property_change_char Q _ _ _ (archimedean_dedekindreals Q)).

(** ** Cauchy complete subsets of a Cauchy complete Archimedean ordered field *)

Section subsets.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    `{!RoundUpStrict Q}.
  Context {F : Type} `{OrderedField F} {Farch : ArchimedeanProperty Q F} `{!IsComplete Q F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.
  Local Notation FS := (cauchy_structure_field Q (F:=F)).

  (** A subset of [F] contains the rationals, and is Cauchy complete when it contains the limit of every Cauchy approximation in it. *)
  Definition ContainsRationals (R : F -> HProp) := forall q : Q, R (' q).

  Definition IsCauchyCompleteSubset (R : F -> HProp)
    := forall x : CauchyApproximation Q (field_close Q (F:=F)),
         (forall e, R (x e)) -> R (field_lim Q x).

  Section subset.
    Context (R : F -> HProp).

    (** The premetric of [F] restricted to a subset. *)
    Definition subset_close (e : Qpos Q) (u v : sig R) := field_close Q e u.1 v.1.

    #[export] Instance ispremetric_subset_close : IsPremetric Q subset_close.
    Proof.
      intros e u v; unfold subset_close; exact _.
    Defined.

    Definition approximation_subset_pr1 (x : CauchyApproximation Q subset_close)
      : CauchyApproximation Q (field_close Q (F:=F))
      := map_cauchy_approximation Q pr1 (fun e u v c => c) x.

    Context (Rq : ContainsRationals R) (Rc : IsCauchyCompleteSubset R).

    (** A Cauchy complete subset containing the rationals inherits the Cauchy structure of [F]. *)
    Definition subset_cauchy_structure : CauchyStructure Q.
    Proof.
      refine (Build_CauchyStructure Q (sig R) subset_close _ (fun q => exist R (' q) (Rq q))
                (fun x => exist R (field_lim Q (approximation_subset_pr1 x))
                           (Rc (approximation_subset_pr1 x) (fun e => (x e).2))) _ _ _ _ _).
      - intros u v c; apply path_sigma_hprop; exact (field_close_eq Q _ _ c).
      - exact (cs_close_rat_rat Q FS).
      - intros q y; exact (cs_close_rat_lim Q FS q (approximation_subset_pr1 y)).
      - intros x r; exact (cs_close_lim_rat Q FS (approximation_subset_pr1 x) r).
      - intros x y; exact (cs_close_lim_lim Q FS (approximation_subset_pr1 x) (approximation_subset_pr1 y)).
    Defined.

    (** The inclusion into [F] is a morphism of Cauchy structures. *)
    Definition cshom_subset_pr1 : CauchyStructureHom Q subset_cauchy_structure FS.
    Proof.
      snapply Build_CauchyStructureHom.
      - exact pr1.
      - exact (fun e u v c => c).
      - intro q; reflexivity.
      - intro x; reflexivity.
      - intros u v p; apply path_ishprop.
    Defined.

    Context (RH : CauchyStructure Q) `{!IsHoTTBookReals Q RH}.

    (** The HoTT book reals are contained in every Cauchy complete subset containing the rationals: the morphism into the subset, followed by the inclusion, is the canonical morphism into [F]. *)
    Definition hottbookreals_to_subset : CauchyStructureHom Q RH subset_cauchy_structure
      := hottbookreals_rec Q RH _.

    Definition hottbookreals_to_subset_pr1 (u : RH)
      : (hottbookreals_to_subset u).1 = hottbookreals_to_field Q RH u
      := hottbookreals_rec_unique Q RH
           (cshom_compose Q cshom_subset_pr1 hottbookreals_to_subset) _ u.

    Definition hottbookreals_to_field_subset (u : RH) : R (hottbookreals_to_field Q RH u)
      := transport R (hottbookreals_to_subset_pr1 u) (hottbookreals_to_subset u).2.
  End subset.

  Section cauchy_reals.
    Context `{Funext} (RH : CauchyStructure Q) `{!IsHoTTBookReals Q RH}.
    Local Notation i := (hottbookreals_to_field Q RH (F:=F)).

    (** The HoTT book reals and the Cauchy reals as subsets of [F]. *)
    Definition subset_hottbookreals (x : F) : HProp := Build_HProp (hfiber i x).

    Definition subset_cauchy_reals (x : F) : HProp := Build_HProp (IsCauchyReal Q F x).

    Definition containsrationals_cauchy_reals : ContainsRationals subset_cauchy_reals
      := fun q => tr (rationals_to_cauchy_reals Q q; cauchy_reals_to_field_rationals Q F q).

    Lemma iscauchycompletesubset_hottbookreals : IsCauchyCompleteSubset subset_hottbookreals.
    Proof.
      intros x h.
      pose (u := fun e => (h e).1).
      assert (c : IsCauchyApproximation Q (cs_close Q RH) u).
      { intros d e; apply (hottbookreals_to_field_reflects_close Q RH).
        unfold u; rewrite (h d).2, (h e).2.
        exact (iscauchyapproximation_approximation Q _ x d e). }
      exists (cs_lim Q RH (Build_CauchyApproximation Q _ u c)).
      rewrite (cshom_lim Q _ _ i).
      apply ap; snapply path_cauchyapproximation; [exact _|]; intro e; exact (h e).2.
    Qed.

    (** The Cauchy reals in [F] are Cauchy complete exactly when they coincide with the HoTT book reals. *)
    Lemma iscauchycompletesubset_cauchy_reals_iff
      : IsCauchyCompleteSubset subset_cauchy_reals
        <-> (forall x, subset_cauchy_reals x <-> subset_hottbookreals x).
    Proof.
      split.
      - intros c x; split.
        + apply Trunc_rec; intros [r p].
          exists (cauchy_reals_to_hottbookreals Q RH r).
          exact (hottbookreals_to_field_cauchy_reals Q RH r @ p).
        + intros [u p]; rewrite <- p.
          exact (hottbookreals_to_field_subset _ containsrationals_cauchy_reals c RH u).
      - intros e x h.
        apply (snd (e _)), iscauchycompletesubset_hottbookreals.
        intro d; exact (fst (e _) (h d)).
    Qed.
  End cauchy_reals.
End subsets.
