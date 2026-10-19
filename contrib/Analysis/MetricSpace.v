(** * Pseudometric and metric spaces *)

From HoTT Require Import Basics Types.Prod Truncations.Core.
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

(** This is one of several notions of closeness in the library: [Closeness] in [Classes/theory/premetric.v] (over the axiomatized rationals), [field_close] and [rational_close] in [CauchyCompleteness.v], and likewise [IsLimit], [IsMetricLimit] and [IsApproximationLimit] (in [CauchyStructure.v]) for limits.  They should eventually be unified, for instance by generalizing [premetric.v] to arbitrary rationals and deriving the others from it. *)

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

  (** A map is uniformly continuous if it merely has a modulus of uniform continuity. *)
  Definition IsUniformlyContinuous {X Y : Type} (closeX : Qpos Q -> X -> X -> Type)
    (closeY : Qpos Q -> Y -> Y -> Type) (f : X -> Y)
    := hexists (IsUniformModulus closeX closeY f).

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

  Section qpos_min.
    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.

    (** The minimum of two positive rationals. *)
    Definition qpos_min (e d : Qpos Q) : Qpos Q
      := match dec (' e < ' d) with
         | inl _ => e
         | inr _ => d
         end.

    Lemma qpos_min_le_l (e d : Qpos Q) : ' (qpos_min e d) ≤ ' e.
    Proof.
      unfold qpos_min; destruct (dec (' e < ' d)) as [lt|nlt].
      - reflexivity.
      - exact (not_lt_le_flip _ _ nlt).
    Qed.

    Lemma qpos_min_le_r (e d : Qpos Q) : ' (qpos_min e d) ≤ ' d.
    Proof.
      unfold qpos_min; destruct (dec (' e < ' d)) as [lt|nlt].
      - exact (lt_le _ _ lt).
      - reflexivity.
    Qed.
  End qpos_min.

  Context {F : Type} `{OrderedField F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  (** The image of a positive rational is positive. *)
  Lemma pos_rationals_to_field_qpos (e : Qpos Q) : (0 : F) < ' (' e).
  Proof.
    rewrite <- (preserves_0 (f:=cast Q F)).
    exact (strictly_order_preserving _ _ _ (pos_is_pos e)).
  Qed.

  (** A distance function induces a closeness relation: [x] and [y] are [e]-close when their distance is less than [e]. *)
  Definition metric_close {X : Type} (d : X -> X -> F) (e : Qpos Q) (x y : X)
    := d x y < ' (' e).

  (** ** Uniqueness of limits *)

  Section uniqueness.
    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
    Context {Farch : ArchimedeanProperty Q F}.

    (** Below a positive element of [F] lies a positive rational. *)
    Lemma merely_qpos_lt (a : F) (lt0a : 0 < a)
      : hexists (fun e : Qpos Q => ' (' e) < a).
    Proof.
      assert (c := archimedean_property Q F 0 a lt0a); strip_truncations.
      destruct c as [q [lt0q ltqa]].
      assert (qpos : 0 < q).
      { apply (strictly_order_reflecting (cast Q F)).
        rewrite (preserves_0 (f:=cast Q F)); exact lt0q. }
      exact (tr (mkQpos q qpos; ltqa)).
    Qed.

    (** An element of [F] below every positive rational is nonpositive. *)
    Lemma nonpos_lt_qpos (a : F) : (forall e : Qpos Q, a < ' (' e)) -> a ≤ 0.
    Proof.
      intros lt; apply not_lt_le_flip; intro lt0a.
      assert (c := merely_qpos_lt a lt0a); strip_truncations; destruct c as [e ltea].
      exact (lt_antisym _ _ (lt e, ltea)).
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

  (** ** Pullbacks and products of pseudometrics *)

  (** A map into a space with a pseudometric induces a pseudometric on its domain. *)
  Definition ispseudometric_pullback {X Y : Type} (p : Y -> X) (d : X -> X -> F)
    `{!IsPseudoMetric d}
    : IsPseudoMetric (fun y z => d (p y) (p z)).
  Proof.
    snapply Build_IsPseudoMetric.
    - intros y z; exact (pseudometric_nonneg (d:=d) _ _).
    - intro y; exact (pseudometric_diag (d:=d) _).
    - intros y z; exact (pseudometric_symmetric (d:=d) _ _).
    - intros x y z; exact (pseudometric_triangle (d:=d) _ _ _).
  Defined.

  Section products.
    Context {X Y : Type} (dX : X -> X -> F) (dY : Y -> Y -> F).

    (** The product of two spaces with distances has the sum of the distances as distance. *)
    Definition prod_dist (p q : X * Y) : F := dX (fst p) (fst q) + dY (snd p) (snd q).

    #[export] Instance ispseudometric_prod `{!IsPseudoMetric dX} `{!IsPseudoMetric dY}
      : IsPseudoMetric prod_dist.
    Proof.
      snapply Build_IsPseudoMetric; unfold prod_dist.
      - intros p q; apply nonneg_plus_compat; apply pseudometric_nonneg.
      - intro p; rewrite 2 pseudometric_diag; apply plus_0_l.
      - intros p q; rewrite (pseudometric_symmetric (fst p)), (pseudometric_symmetric (snd p)).
        reflexivity.
      - intros p q r.
        refine (transitivity (plus_le_compat _ _ _ _ (pseudometric_triangle _ (fst q) _)
                  (pseudometric_triangle _ (snd q) _)) _).
        apply eq_le.
        rewrite <- 2 plus_assoc; apply ap.
        rewrite 2 plus_assoc; apply (ap (+ _)), plus_comm.
    Defined.

    (** If a sum of two nonnegative elements is zero, then so is the first summand. *)
    Local Lemma nonneg_plus_eq_0_l (u v : F) : 0 ≤ u -> 0 ≤ v -> u + v = 0 -> u = 0.
    Proof.
      intros u0 v0 p; apply (antisymmetry (≤)); [|exact u0].
      rewrite <- p; exact (fst (nonneg_plus_le_compat_r u v) v0).
    Qed.

    #[export] Instance ismetric_prod `{!IsMetric dX} `{!IsMetric dY} : IsMetric prod_dist.
    Proof.
      snapply Build_IsMetric; [exact _|].
      intros [x y] [x' y'] p; unfold prod_dist in p; cbn in p.
      assert (nx := pseudometric_nonneg (d:=dX) x x').
      assert (ny := pseudometric_nonneg (d:=dY) y y').
      apply path_prod; cbn; apply metric_separated.
      - exact (nonneg_plus_eq_0_l _ _ nx ny p).
      - rewrite plus_comm in p; exact (nonneg_plus_eq_0_l _ _ ny nx p).
    Defined.

  End products.

  Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.

  Local Instance orderpreserving_qinc' : OrderPreserving (cast Q F)
    := full_pseudo_order_preserving.

  (** Halves add up in [F]. *)
  Local Lemma qinc_split2 (e : Qpos Q) : ' (' e) = ' (' (e / 2)) + ' (' (e / 2)) :> F.
  Proof.
    rewrite <- (preserves_plus (f:=cast Q F)).
    exact (ap (fun d : Qpos Q => ' (' d)) (pos_split2 e)).
  Qed.

  Section product_maps.
    Context {X Y X' Y' : Type} (dX : X -> X -> F) (dY : Y -> Y -> F)
      (dX' : X' -> X' -> F) (dY' : Y' -> Y' -> F)
      `{!IsPseudoMetric dX} `{!IsPseudoMetric dY}.

    (** A product of uniformly continuous maps is uniformly continuous, with the minimum of the moduli at [e / 2] as modulus. *)
    Lemma isuniformmodulus_prod (f : X -> X') (g : Y -> Y') (wf wg : Qpos Q -> Qpos Q)
      (fw : IsUniformModulus (metric_close dX) (metric_close dX') f wf)
      (gw : IsUniformModulus (metric_close dY) (metric_close dY') g wg)
      : IsUniformModulus (metric_close (prod_dist dX dY))
          (metric_close (prod_dist dX' dY')) (functor_prod f g)
          (fun e => qpos_min (wf (e / 2)) (wg (e / 2))).
    Proof.
      intros e [x y] [x' y'] c; unfold metric_close, prod_dist in *; cbn in *.
      assert (nx := pseudometric_nonneg (d:=dX) x x').
      assert (ny := pseudometric_nonneg (d:=dY) y y').
      rewrite (qinc_split2 e).
      apply plus_lt_compat.
      - apply fw; unfold metric_close.
        refine (le_lt_trans _ _ _ (fst (nonneg_plus_le_compat_r _ _) ny) _).
        refine (lt_le_trans _ _ _ c _).
        apply (order_preserving (cast Q F)), qpos_min_le_l.
      - apply gw; unfold metric_close.
        refine (le_lt_trans _ _ _ (fst (nonneg_plus_le_compat_l _ _) nx) _).
        refine (lt_le_trans _ _ _ c _).
        apply (order_preserving (cast Q F)), qpos_min_le_r.
    Qed.
  End product_maps.

  (** The diagonal map has modulus [e / 2]. *)
  Lemma isuniformmodulus_diagonal {X : Type} (d : X -> X -> F)
    : IsUniformModulus (metric_close d) (metric_close (prod_dist d d))
        (fun x => (x, x)) (fun e => e / 2).
  Proof.
    intros e x y c; unfold metric_close, prod_dist in *; cbn.
    rewrite (qinc_split2 e); exact (plus_lt_compat _ _ _ _ c c).
  Qed.

  (** If [f] has modulus [w] and [g] on the product has modulus [v], then [fun x => g (x, f x)] is uniformly continuous with the modulus below. *)
  Lemma isuniformmodulus_graph {X Y Z : Type} (dX : X -> X -> F) (dY : Y -> Y -> F)
    (dZ : Z -> Z -> F) `{!IsPseudoMetric dX} `{!IsPseudoMetric dY}
    (f : X -> Y) (g : X * Y -> Z) (w v : Qpos Q -> Qpos Q)
    (fw : IsUniformModulus (metric_close dX) (metric_close dY) f w)
    (gv : IsUniformModulus (metric_close (prod_dist dX dY)) (metric_close dZ) g v)
    : IsUniformModulus (metric_close dX) (metric_close dZ) (fun x => g (x, f x))
        (fun e => qpos_min (v e / 2) (w (v e / 2)) / 2).
  Proof.
    refine (isuniformmodulus_compose _ (metric_close (prod_dist dX dY)) _
              (functor_prod idmap f o (fun x => (x, x))) g
              (fun e => qpos_min (e / 2) (w (e / 2)) / 2) v _ gv).
    exact (isuniformmodulus_compose _ (metric_close (prod_dist dX dX)) _ _ _ _ _
             (isuniformmodulus_diagonal dX)
             (isuniformmodulus_prod dX dX dX dY idmap f idmap w
                (isuniformmodulus_idmap _) fw)).
  Qed.


End convergence.
