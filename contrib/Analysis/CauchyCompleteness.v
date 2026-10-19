(** * Cauchy completeness of Archimedean ordered fields *)

From HoTT Require Import Basics Truncations.Core.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  interfaces.cauchy
  implementations.peano_naturals
  theory.rings
  theory.rationals
  orders.orders
  orders.rings
  orders.rationals.
From HoTT_Contrib.Analysis Require Import MetricSpace.

(** In an Archimedean ordered field, limits of sequences are unique, so the type of limits of a sequence is a proposition. Hence a limit that merely exists can be computed, and so can a limit of a sequence that merely has a modulus of Cauchy convergence, if the field is Cauchy complete. *)

Section completeness.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
  Context {F : Type} `{OrderedField F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  (** ** Closeness in an ordered field *)

  (** Two elements [u] and [v] of [F] are [e]-close when [|u - v| < e]. We state this without the absolute value, as in [CauchyModulus] and [IsLimit]. *)
  Definition field_close (e : Qpos Q) (u v : F) := - ' (' e) < u - v < ' (' e).

  (** Two rationals [u] and [v] are [e]-close when [|u - v| < e]. *)
  Definition rational_close (e : Qpos Q) (u v : Q) := - ' e < u - v < ' e.

  Lemma rational_close_refl (e : Qpos Q) (q : Q) : rational_close e q q.
  Proof.
    unfold rational_close; rewrite plus_negate_r; split.
    - apply flip_pos_negate, is_pos.
    - apply is_pos.
  Qed.

  (** The inclusion of the rationals preserves closeness. *)
  Lemma field_close_rationals (e : Qpos Q) (u v : Q)
    : rational_close e u v -> field_close e (' u) (' v).
  Proof.
    intros [lo hi]; unfold field_close.
    rewrite <- (preserves_minus (f:=cast Q F)), <- (preserves_negate (f:=cast Q F)).
    split; rapply strictly_order_preserving; assumption.
  Qed.

  (** It also reflects closeness. *)
  Lemma rational_close_field_close (e : Qpos Q) (u v : Q)
    : field_close e (' u) (' v) -> rational_close e u v.
  Proof.
    intros [lo hi]; unfold rational_close.
    rewrite <- (preserves_minus (f:=cast Q F)) in lo, hi.
    rewrite <- (preserves_negate (f:=cast Q F)) in lo.
    exact (strictly_order_reflecting _ _ _ lo, strictly_order_reflecting _ _ _ hi).
  Qed.

  (** Closeness of rationals satisfies the triangle inequality. *)
  Lemma rational_close_triangle (d e : Qpos Q) (a b c : Q)
    : rational_close d a b -> rational_close e b c -> rational_close (d + e) a c.
  Proof.
    intros [lo hi] [lo' hi']; unfold rational_close.
    assert (p : a - c = (a - b) + (b - c)).
    { rewrite <- (plus_assoc a (- b) (b - c)), (plus_assoc (- b) b (- c)).
      rewrite plus_negate_l, plus_0_l; reflexivity. }
    change (' (d + e)) with (' d + ' e).
    rewrite p, negate_plus_distr; split; apply plus_lt_compat; assumption.
  Qed.

  (** Bounds add up. *)
  Lemma lt_bound_plus (a b p q : F) (ap : - p < a < p) (bq : - q < b < q)
    : - (p + q) < a + b < p + q.
  Proof.
    rewrite negate_plus_distr; split.
    - exact (plus_lt_compat _ _ _ _ (fst ap) (fst bq)).
    - exact (plus_lt_compat _ _ _ _ (snd ap) (snd bq)).
  Qed.

  Lemma le_lt_bound_plus (a b p q : F) (ap : - p ≤ a ≤ p) (bq : - q < b < q)
    : - (p + q) < a + b < p + q.
  Proof.
    rewrite negate_plus_distr; split.
    - exact (plus_le_lt_compat _ _ _ _ (fst ap) (fst bq)).
    - exact (plus_le_lt_compat _ _ _ _ (snd ap) (snd bq)).
  Qed.

  Lemma lt_le_bound_plus (a b p q : F) (ap : - p < a < p) (bq : - q ≤ b ≤ q)
    : - (p + q) < a + b < p + q.
  Proof.
    rewrite (plus_comm a b), (plus_comm p q).
    exact (le_lt_bound_plus b a q p bq ap).
  Qed.

  Lemma lt_bound_negate (a p : F) (ap : - p < a < p) : - p < - a < p.
  Proof.
    split.
    - apply (flip_lt_negate a p); exact (snd ap).
    - apply flip_lt_negate_l; exact (fst ap).
  Qed.

  Lemma le_bound_negate (a p : F) (ap : - p ≤ a ≤ p) : - p ≤ - a ≤ p.
  Proof.
    split.
    - apply (flip_le_negate a p); exact (snd ap).
    - rewrite <- (negate_involutive p); apply (flip_le_negate (- p) a); exact (fst ap).
  Qed.

  (** If [l] is a limit of [x], then [- l] is a limit of [- x]. *)
  Lemma islimit_negate (x : nat -> F) (l : F) (islim : IsLimit Q F x l)
    : IsLimit Q F (fun n => - x n) (- l).
  Proof.
    intro e; refine (Trunc_functor (-1) _ (islim e)); intros [N close].
    exists N; intros n len.
    rewrite <- negate_plus_distr; exact (lt_bound_negate _ _ (close n len)).
  Qed.

  Lemma field_close_symmetric (e : Qpos Q) (u v : F)
    : field_close e u v -> field_close e v u.
  Proof.
    intro c; unfold field_close.
    rewrite (negate_swap_r v u); exact (lt_bound_negate _ _ c).
  Qed.

  Lemma field_close_triangle (e d : Qpos Q) (u v w : F)
    : field_close e u v -> field_close d v w -> field_close (e + d) u w.
  Proof.
    intros c c'; unfold field_close.
    change (' (' (e + d))) with (' (' e + ' d) : F).
    rewrite (preserves_plus (f:=cast Q F)), <- (plus_minus_telescope u v w).
    exact (lt_bound_plus _ _ _ _ c c').
  Qed.

  (** Closeness is preserved by enlarging the bound. *)
  Lemma field_close_weaken (e d : Qpos Q) (u v : F) (ltde : ' e < ' d)
    : field_close e u v -> field_close d u v.
  Proof.
    intro c; exact (between_weaken _ _ _ c (strictly_order_preserving (cast Q F) _ _ ltde)).
  Qed.

  (** Closeness is a bound on the absolute value of the difference. *)
  Lemma field_close_iff_abs `{!Abs F} (e : Qpos Q) (u v : F)
    : field_close e u v <-> abs (u - v) < ' (' e).
  Proof.
    split.
    - intros [lo hi]; exact (abs_lt _ _ lo hi).
    - intro lt; split.
      + apply flip_lt_negate_l.
        exact (le_lt_trans _ _ _ (negate_le_abs (u - v)) lt).
      + exact (le_lt_trans _ _ _ (le_abs (u - v)) lt).
  Qed.

  Context {Farch : ArchimedeanProperty Q F}.

  (** In an Archimedean ordered field, elements which are [e]-close for every [e] are equal. *)
  Lemma field_close_eq (u v : F) (c : forall e : Qpos Q, field_close e u v) : u = v.
  Proof.
    apply (antisymmetry (≤)); apply flip_nonpos_minus, (nonpos_lt_qpos Q); intro e.
    - exact (snd (c e)).
    - exact (snd (field_close_symmetric e u v (c e))).
  Qed.

  (** ** Uniqueness of limits *)

  Section limits.
    Context (x : nat -> F).

    (** Limits of sequences are unique. *)
    Lemma limit_unique (l l' : F) (islim : IsLimit Q F x l) (islim' : IsLimit Q F x l')
      : l = l'.
    Proof.
      apply field_close_eq; intro e.
      assert (c := islim (e / 2)).
      assert (c' := islim' (e / 2)).
      strip_truncations; destruct c as [N close], c' as [N' close'].
      set (n := Nat.Core.nat_max N N').
      rewrite (pos_split2 e).
      apply (field_close_triangle _ _ _ (x n)).
      - exact (close n (le_nat_max_l N N')).
      - apply field_close_symmetric; exact (close' n (le_nat_max_r N N')).
    Qed.

    #[export] Instance ishprop_islimit `{Funext} (l : F) : IsHProp (IsLimit Q F x l).
    Proof.
      unfold IsLimit; exact _.
    Defined.

    (** The type of limits of a sequence is a proposition. *)
    #[export] Instance ishprop_limit `{Funext} : IsHProp {l : F & IsLimit Q F x l}.
    Proof.
      apply hprop_allpath; intros [l islim] [l' islim'].
      apply path_sigma_hprop; exact (limit_unique l l' islim islim').
    Defined.

    (** Hence a limit that merely exists can be computed. *)
    Definition limit_merely `{Funext} : hexists (IsLimit Q F x) -> {l : F & IsLimit Q F x l}
      := Trunc_rec idmap.

    (** If a limit can be computed from a modulus of Cauchy convergence, then the mere existence of a modulus suffices to compute it. *)
    Definition limit_merely_modulus `{Funext}
      (lim : forall M, CauchyModulus Q F x M -> {l : F & IsLimit Q F x l})
      : hexists (CauchyModulus Q F x) -> {l : F & IsLimit Q F x l}
      := Trunc_rec (fun Mmod => lim Mmod.1 Mmod.2).

  End limits.

  (** In a Cauchy complete Archimedean ordered field, a sequence which merely has a modulus of Cauchy convergence has a limit. *)
  Definition limit_complete `{Funext} `{!IsComplete Q F} (x : nat -> F)
    : hexists (CauchyModulus Q F x) -> {l : F & IsLimit Q F x l}
    := limit_merely_modulus x (is_complete Q F x).

End completeness.
