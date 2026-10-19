(** * Functions that lift to locators *)

(** A function on an Archimedean ordered field lifts to locators if it comes with a way to compute a locator for its value from a locator for its argument. This is an abstract notion of computability, which is independent of continuity: constant functions are continuous but need not lift to locators, and with excluded middle every function lifts to locators. *)

From HoTT Require Import Basics Truncations.Core ExcludedMiddle.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  theory.rings
  theory.rationals
  orders.orders
  orders.rings
  orders.rationals.
From HoTT.Analysis Require Import Locator.
From HoTT_Contrib.Analysis Require Import MetricSpace CauchyCompleteness.

Section lifts.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qtrich : Trichotomy (<)}.
  Context (F : Type) `{Forderedfield : OrderedField F}.

  Local Existing Instance qinc.

  (** ** Lifting to locators *)

  (** A function [f] lifts to locators if it is equipped with a map from locators for [x] to locators for [f x]. This is structure, not a property. *)
  Definition LiftsToLocators (f : F -> F) := forall x : F, locator Q F x -> locator Q F (f x).

  (** ** Continuity *)

  (** A function [f] is continuous at [x] if for every [e] there merely is a [d] such that the values at points [d]-close to [x] are [e]-close to [f x]. Closeness is [field_close], that is, [|u - v| < e]. *)
  Definition IsContinuousAt (f : F -> F) (x : F)
    := forall e : Qpos Q, hexists (fun d : Qpos Q =>
         forall y : F, field_close Q d x y -> field_close Q e (f x) (f y)).

  (** A function is pointwise continuous if it is continuous at every point. *)
  Definition IsPointwiseContinuous (f : F -> F) := forall x : F, IsContinuousAt f x.

  (** If [f] is continuous at [x], so is [- f]. *)
  Lemma iscontinuousat_negate (f : F -> F) (x : F) (cont : IsContinuousAt f x)
    : IsContinuousAt (fun y => - f y) x.
  Proof.
    intro e; refine (Trunc_functor (-1) _ (cont e)); intros [d close].
    exists d; intros y cxy.
    unfold field_close; rewrite <- negate_plus_distr.
    exact (lt_bound_negate _ _ (close y cxy)).
  Qed.

  (** If [f] is continuous at [x] and [t < f x], then [t < f y] for all [y] close enough to [x]. *)
  Lemma iscontinuousat_lt {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Farch : ArchimedeanProperty Q F} (f : F -> F) (x : F) (cont : IsContinuousAt f x)
    (t : F) (lt : t < f x)
    : hexists (fun d : Qpos Q => forall y : F, field_close Q d x y -> t < f y).
  Proof.
    assert (e := merely_qpos_lt Q (f x - t) (snd (flip_pos_minus _ _) lt)).
    strip_truncations; destruct e as [e lte].
    refine (Trunc_functor (-1) _ (cont e)); intros [d close].
    exists d; intros y cxy.
    assert (lt' := snd (close y cxy)); change (f x - f y < ' (' e)) in lt'.
    apply (fst (flip_lt_minus_r _ _ _)) in lte.
    apply (fst (flip_lt_minus_l _ _ _)) in lt'.
    apply (strictly_order_reflecting (' (' e) +)).
    exact (transitivity lte lt').
  Qed.

  (** A modulus of uniform continuity for [f] on the interval [[a, b]]: a modulus of uniform continuity, in the sense of [IsUniformModulus], for the restriction of [f] to the interval. This is structure. *)
  Definition UniformModulusOn (a b : F) (f : F -> F)
    := {w : Qpos Q -> Qpos Q &
         IsUniformModulus Q (fun e (x y : {z : F & a ≤ z ≤ b}) => field_close Q e x.1 y.1)
           (field_close Q) (fun x => f x.1) w}.

  (** ** Lifting to locators and continuity are independent *)

  (** If all constant functions lift to locators, then every element has a locator, by evaluating the constant function at [0]. *)
  Definition locator_lifts_constant (lifts : forall s : F, LiftsToLocators (fun _ => s))
    (x : F)
    : locator Q F x
    := lifts x (' 0) (locator_left Q F 0).

  (** Assuming excluded middle, the function which is [1] on positive elements and [0] elsewhere lifts to locators, since every element has a locator, but it is not continuous at [0]. *)
  Section classical.
    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q} `{ExcludedMiddle}.

    Definition step_function (x : F) : F
      := match LEM (0 < x) _ with
         | inl _ => 1
         | inr _ => 0
         end.

    Definition lifts_step_function : LiftsToLocators step_function
      := fun x _ => all_reals_locators Q F (step_function x).

    Lemma not_iscontinuousat_step_function : ~ IsContinuousAt step_function 0.
    Proof.
      intro cont.
      assert (c := cont 1); strip_truncations; destruct c as [d close].
      (* The element [d / 2] is [d]-close to [0], but the values there are [1] apart. *)
      set (y := ' (' (d / 2)) : F).
      assert (ypos : 0 < y) by exact (pos_rationals_to_field_qpos Q (d / 2)).
      assert (dpos := pos_rationals_to_field_qpos Q (F:=F) d).
      assert (ltyd : y < ' (' d)).
      { exact (strictly_order_preserving _ _ _ (qpos_half_lt d)). }
      assert (c : field_close Q d 0 y).
      { unfold field_close; rewrite plus_0_l; split.
        - exact (snd (flip_lt_negate _ _) ltyd).
        - exact (transitivity (fst (flip_pos_negate _) ypos) dpos). }
      assert (c' := fst (close y c)).
      unfold step_function in c'.
      destruct (LEM (0 < 0) _) as [lt00|_]; [exact (irreflexivity _ _ lt00)|].
      destruct (LEM (0 < y) _) as [_|nlt]; [|exact (nlt ypos)].
      rewrite plus_0_l in c'.
      change (' (' (1 : Qpos Q))) with (' (1 : Q)) in c'.
      rewrite (preserves_1 (f:=cast Q F)) in c'.
      exact (irreflexivity _ _ c').
    Qed.
  End classical.

End lifts.
