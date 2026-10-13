(** * Pseudometric and metric spaces *)

From HoTT Require Import Basics Truncations.Core.
From HoTT.Universes Require Import HSet.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  implementations.peano_naturals
  theory.rings
  theory.rationals
  orders.orders
  orders.rings
  orders.rationals.

(** We work with distances valued in an arbitrary ordered field [F], with the closeness relation [d x y < e] for positive rationals [e] in some rationals [Q]. *)

(** ** Pseudometrics and metrics *)

Section metric.
  Context {F : Type} `{OrderedField F}.

  (** A pseudometric on [X] is a nonnegative distance function which is zero on the diagonal, symmetric and satisfies the triangle inequality. *)
  Class IsPseudoMetric {X : Type} (d : X -> X -> F) := {
    pseudometric_nonneg : forall x y, 0 ≤ d x y;
    pseudometric_diag : forall x, d x x = 0;
    pseudometric_symmetric : forall x y, d x y = d y x;
    pseudometric_triangle : forall x y z, d x z ≤ d x y + d y z
  }.

  (** A metric is a pseudometric which separates points. *)
  Class IsMetric {X : Type} (d : X -> X -> F) := {
    metric_pseudometric :: IsPseudoMetric d;
    metric_separated : forall x y, d x y = 0 -> x = y
  }.

  (** A type with a metric is a set. *)
  Lemma ishset_metric {X : Type} (d : X -> X -> F) `{!IsMetric d} : IsHSet X.
  Proof.
    exact (@ishset_hrel_subpaths X (fun x y => d x y = 0)
             pseudometric_diag _ metric_separated).
  Defined.

  (** The Euclidean distance. *)
  #[export] Instance ismetric_abs_minus `{!Abs F} : IsMetric (fun x y : F => abs (x - y)).
  Proof.
    snapply Build_IsMetric; [snapply Build_IsPseudoMetric|].
    - intros x y; apply abs_nonneg.
    - intro x; change (abs (x - x) = 0); rewrite plus_negate_r; apply abs_0.
    - intros x y; apply abs_minus_swap.
    - intros x y z; change (abs (x - z) ≤ abs (x - y) + abs (y - z)).
      assert (p : (x - y) + (y - z) = x - z).
      { rewrite <- (plus_assoc x (- y) (y - z)), (plus_assoc (- y) y (- z)).
        rewrite plus_negate_l, plus_0_l; reflexivity. }
      rewrite <- p; apply abs_triangle.
    - intros x y p; apply equal_by_zero_sum, abs_eq_0, p.
  Defined.

End metric.

(** ** Premetrics, convergence and uniform continuity *)

Section convergence.
  (** The order on [Q] is at the level of [Q], as for [Qpos], so that instances are found for closeness relations passed as arguments. *)
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q}.

  (** A premetric on [X] is a family of relations [close e] indexed by the positive rationals [e], where [close e x y] says that [x] and [y] are [e]-close. Closeness is a proposition, and no other axioms are imposed. The definitions below make sense for any family of relations. *)
  Class IsPremetric {X : Type} (close : Qpos Q -> X -> X -> Type)
    := ishprop_premetric : forall e x y, IsHProp (close e x y).
  #[export] Existing Instance ishprop_premetric.

  Section premetric.
    Context {X : Type} (close : Qpos Q -> X -> X -> Type).

    (** A modulus of Cauchy convergence for a sequence. *)
    Class MetricCauchyModulus (x : nat -> X) (M : Qpos Q -> nat)
      := metric_cauchy_convergence : forall (e : Qpos Q) (m n : nat),
           (M e <= m)%nat -> (M e <= n)%nat -> close e (x m) (x n).

    (** A limit of a sequence. *)
    Class IsMetricLimit (x : nat -> X) (l : X)
      := is_metric_limit : forall e : Qpos Q,
           hexists (fun N : nat => forall n : nat, (N <= n)%nat -> close e (x n) l).

    (** Cauchy completeness is the structure of a limit operator, which computes a limit of each sequence with a modulus of Cauchy convergence. *)
    Class MetricCauchyComplete := {
      metric_limit : forall (x : nat -> X) (M : Qpos Q -> nat),
        MetricCauchyModulus x M -> X;
      ismetriclimit_metric_limit : forall (x : nat -> X) (M : Qpos Q -> nat)
        (Mmod : MetricCauchyModulus x M), IsMetricLimit x (metric_limit x M Mmod)
    }.

    (** A limit of a sequence is a limit of its tail. *)
    Lemma ismetriclimit_tail (x : nat -> X) (l : X) (islim : IsMetricLimit x l)
      : IsMetricLimit (fun n => x (S n)) l.
    Proof.
      intro e; assert (c := islim e); strip_truncations; apply tr.
      destruct c as [N close'].
      exists N; intros n leNn.
      exact (close' (S n) (leq_succ_r leNn)).
    Defined.

  End premetric.

  (** A modulus of uniform continuity for a map. *)
  Class IsUniformModulus {X Y : Type} (closeX : Qpos Q -> X -> X -> Type)
    (closeY : Qpos Q -> Y -> Y -> Type) (f : X -> Y) (w : Qpos Q -> Qpos Q)
    := uniform_modulus : forall (e : Qpos Q) (x y : X),
         closeX (w e) x y -> closeY e (f x) (f y).

  Section uniform.
    Context {X Y Z : Type} (closeX : Qpos Q -> X -> X -> Type)
      (closeY : Qpos Q -> Y -> Y -> Type) (closeZ : Qpos Q -> Z -> Z -> Type).

    Definition isuniformmodulus_idmap : IsUniformModulus closeX closeX idmap idmap
      := fun e x y c => c.

    (** Moduli compose in the reverse order. *)
    Definition isuniformmodulus_compose (f : X -> Y) (g : Y -> Z) (w v : Qpos Q -> Qpos Q)
      (fw : IsUniformModulus closeX closeY f w) (gv : IsUniformModulus closeY closeZ g v)
      : IsUniformModulus closeX closeZ (g o f) (w o v)
      := fun e x y c => gv e _ _ (fw (v e) x y c).

    (** A uniformly continuous map sends a sequence with a modulus of Cauchy convergence to one with a modulus. *)
    Definition metriccauchymodulus_uniform (f : X -> Y) (w : Qpos Q -> Qpos Q)
      (fw : IsUniformModulus closeX closeY f w) (x : nat -> X) (M : Qpos Q -> nat)
      (xM : MetricCauchyModulus closeX x M)
      : MetricCauchyModulus closeY (f o x) (M o w)
      := fun e m n lem len => fw e _ _ (xM (w e) m n lem len).

    (** A map preserves limits if it sends limits of sequences to limits of the image sequences. *)
    Definition PreservesMetricLimits (f : X -> Y)
      := forall (x : nat -> X) (l : X),
           IsMetricLimit closeX x l -> IsMetricLimit closeY (f o x) (f l).

    (** Uniformly continuous maps preserve limits. *)
    Lemma preservesmetriclimits_uniform (f : X -> Y) (w : Qpos Q -> Qpos Q)
      (fw : IsUniformModulus closeX closeY f w)
      : PreservesMetricLimits f.
    Proof.
      intros x l islim e.
      assert (c := islim (w e)); strip_truncations; apply tr.
      destruct c as [N close].
      exists N; intros n leNn.
      exact (fw e _ _ (close n leNn)).
    Defined.

  End uniform.

  Context {F : Type} `{OrderedField F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  (** A distance function induces a premetric: [x] and [y] are [e]-close when their distance is less than [e]. *)
  Definition metric_close {X : Type} (d : X -> X -> F) (e : Qpos Q) (x y : X)
    := d x y < ' (' e).

  #[export] Instance ispremetric_metric_close {X : Type} (d : X -> X -> F)
    : IsPremetric (metric_close d).
  Proof.
    intros e x y; unfold metric_close; exact _.
  Defined.

  (** ** Uniqueness of limits *)

  Section uniqueness.
    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
    Context {Farch : ArchimedeanProperty Q F}.

    (** An element of [F] below every positive rational is nonpositive. *)
    Lemma nonpos_lt_qpos (a : F) : (forall e : Qpos Q, a < ' (' e)) -> a ≤ 0.
    Proof.
      intros lt; apply not_lt_le_flip; intro lt0a.
      assert (c := archimedean_property Q F 0 a lt0a); strip_truncations.
      destruct c as [q [lt0q ltqa]].
      assert (qpos : 0 < q).
      { apply (strictly_order_reflecting (cast Q F)).
        rewrite (preserves_0 (f:=cast Q F)); exact lt0q. }
      exact (lt_antisym _ _ (lt (mkQpos q qpos), ltqa)).
    Qed.

    Context {X : Type} (d : X -> X -> F).

    (** Two limits of the same sequence have distance zero. *)
    Lemma metric_limit_distance_zero `{!IsPseudoMetric d} (x : nat -> X) (l l' : X)
      (islim : IsMetricLimit (metric_close d) x l)
      (islim' : IsMetricLimit (metric_close d) x l')
      : d l l' = 0.
    Proof.
      apply (antisymmetry (≤)); [|apply pseudometric_nonneg].
      apply nonpos_lt_qpos; intro e.
      assert (c := islim (e / 2)).
      assert (c' := islim' (e / 2)).
      strip_truncations; destruct c as [N close], c' as [N' close'].
      set (n := Nat.Core.nat_max N N').
      refine (le_lt_trans _ _ _ (pseudometric_triangle (d:=d) l (x n) l') _).
      rewrite (pos_split2 e), (preserves_plus (f:=cast Q F)).
      apply plus_lt_compat.
      - rewrite (pseudometric_symmetric (d:=d)).
        exact (close n (le_nat_max_l N N')).
      - exact (close' n (le_nat_max_r N N')).
    Qed.

    (** In a metric space, limits are unique. *)
    Lemma metric_limit_unique `{!IsMetric d} (x : nat -> X) (l l' : X)
      (islim : IsMetricLimit (metric_close d) x l)
      (islim' : IsMetricLimit (metric_close d) x l')
      : l = l'.
    Proof.
      exact (metric_separated l l' (metric_limit_distance_zero x l l' islim islim')).
    Qed.

  End uniqueness.

End convergence.
