Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.theory.fields
  HoTT.Classes.theory.apartness.
Require Export
  HoTT.Classes.theory.rings.

Generalizable Variables F f R.

Section contents.
Context `{IsDecField F} `{forall x y: F, Decidable (x = y)}.

(* Add Ring F : (stdlib_ring_theory F). *)

Global Instance decfield_zero_product : ZeroProduct F.
Proof.
intros x y E.
destruct (dec (x = 0)) as [? | Ex];auto.
right.
rewrite <-(mult_1_r y), <-(dec_recip_inverse x) by assumption.
rewrite associativity, (commutativity y), E.
apply mult_0_l.
Qed.

Global Instance decfield_integral_domain : IsIntegralDomain F.
Proof.
split; try apply _.
Qed.

Lemma dec_recip_1: / 1 = 1.
Proof.
rewrite <-(rings.mult_1_l (/1)).
apply dec_recip_inverse.
solve_propholds.
Qed.

Lemma dec_recip_distr (x y: F): / (x * y) = / x * / y.
Proof.
destruct (dec (x = 0)) as [Ex|Ex].
- rewrite Ex, left_absorb, dec_recip_0. apply symmetry,mult_0_l.
- destruct (dec (y = 0)) as [Ey|Ey].
  + rewrite Ey, dec_recip_0, !mult_0_r. apply dec_recip_0.
  + assert (x * y <> 0) as Exy by (apply mult_ne_0;trivial).
    apply (left_cancellation_ne_0 (.*.) (x * y)); trivial.
    transitivity (x / x * (y / y)).
    * rewrite !dec_recip_inverse by assumption. rewrite mult_1_l;apply reflexivity.
    * rewrite !dec_recip_inverse by assumption.
      rewrite mult_assoc, (mult_comm x), <-(mult_assoc y).
      rewrite dec_recip_inverse by assumption.
      rewrite (mult_comm y), <-mult_assoc.
      rewrite dec_recip_inverse by assumption. reflexivity.
Qed.

Lemma dec_recip_zero x : / x = 0 <-> x = 0.
Proof.
split; intros E.
- apply stable. intros Ex.
  destruct (is_ne_0 1).
  rewrite <-(dec_recip_inverse x), E by assumption.
  apply mult_0_r.
- rewrite E. apply dec_recip_0.
Qed.

Lemma dec_recip_ne_0_iff x : / x <> 0 <-> x <> 0.
Proof.
split; intros E1 E2; destruct E1; apply dec_recip_zero;trivial.
do 2 apply (snd (dec_recip_zero _)). trivial.
Qed.

Instance dec_recip_ne_0 x : PropHolds (x <> 0) -> PropHolds (/x <> 0).
Proof.
intro.
apply (snd (dec_recip_ne_0_iff _)).
trivial.
Qed.

Lemma equal_by_one_quotient (x y : F) : x / y = 1 -> x = y.
Proof.
intro Exy.
destruct (dec (y = 0)) as [Ey|Ey].
- destruct (is_ne_0 1).
  rewrite <- Exy, Ey, dec_recip_0. apply mult_0_r.
- apply (right_cancellation_ne_0 (.*.) (/y)).
  + apply dec_recip_ne_0. trivial.
  + rewrite dec_recip_inverse;trivial.
Qed.

Global Instance dec_recip_inj: IsInjective (/).
Proof.
repeat (split; try apply _).
intros x y E.
destruct (dec (y = 0)) as [Ey|Ey].
- rewrite Ey in *. rewrite dec_recip_0 in E.
  apply dec_recip_zero. trivial.
- apply (right_cancellation_ne_0 (.*.) (/y)).
  + apply dec_recip_ne_0. trivial.
  + rewrite dec_recip_inverse by assumption.
    rewrite <-E, dec_recip_inverse;trivial.
    apply dec_recip_ne_0_iff. rewrite E.
    apply dec_recip_ne_0. trivial.
Qed.

Global Instance dec_recip_involutive: Involutive (/).
Proof.
intros x. destruct (dec (x = 0)) as [Ex|Ex].
- rewrite Ex, !dec_recip_0. trivial.
- apply (right_cancellation_ne_0 (.*.) (/x)).
  + apply dec_recip_ne_0. trivial.
  + rewrite dec_recip_inverse by assumption.
    rewrite mult_comm, dec_recip_inverse.
    * reflexivity.
    * apply dec_recip_ne_0. trivial.
Qed.

Lemma equal_dec_quotients (a b c d : F) : b <> 0 -> d <> 0 ->
  (a * d = c * b <-> a / b = c / d).
Proof.
split; intro E.
- apply (right_cancellation_ne_0 (.*.) b);trivial.
  apply (right_cancellation_ne_0 (.*.) d);trivial.
  transitivity (a * d * (b * /b));[|
  transitivity (c * b * (d * /d))].
  + rewrite <-!(mult_assoc a). apply ap.
    rewrite (mult_comm d), (mult_comm _ b).
    reflexivity.
  + rewrite E, dec_recip_inverse, dec_recip_inverse;trivial.
  + rewrite <-!(mult_assoc c). apply ap.
    rewrite (mult_comm d), mult_assoc, (mult_comm b).
    reflexivity.
- transitivity (a * d * 1);[rewrite mult_1_r;reflexivity|].
  rewrite <-(dec_recip_inverse b);trivial.
  transitivity (c * b * 1);[|rewrite mult_1_r;reflexivity].
  rewrite <-(dec_recip_inverse d);trivial.
  rewrite mult_comm, <-mult_assoc, (mult_assoc _ a), (mult_comm _ a), E.
  rewrite <-mult_assoc. rewrite (mult_comm _ d).
  rewrite mult_assoc, (mult_comm c). reflexivity.
Qed.

Lemma dec_quotients (a c b d : F)
  : b <> 0 -> d <> 0 -> a / b + c / d = (a * d + c * b) / (b * d).
Proof.
intros A B.
assert (a / b = (a * d) / (b * d)) as E1.
- apply equal_dec_quotients;auto.
  + solve_propholds.
  + rewrite (mult_comm b);apply associativity.
- assert (c / d = (b * c) / (b * d)) as E2.
  + apply equal_dec_quotients;trivial.
    * solve_propholds.
    * rewrite mult_assoc, (mult_comm c). reflexivity.
  + rewrite E1, E2.
    rewrite (mult_comm c b).
    apply symmetry, simple_distribute_r.
Qed.

Lemma dec_recip_swap_l x y: x / y = / (/ x * y).
Proof.
rewrite dec_recip_distr, involutive. reflexivity.
Qed.

Lemma dec_recip_swap_r x y: / x * y = / (x / y).
Proof.
rewrite dec_recip_distr, involutive.
reflexivity.
Qed.

Lemma dec_recip_negate x : -(/ x) = / (-x).
Proof.
destruct (dec (x = 0)) as [Ex|Ex].
- rewrite Ex, negate_0, dec_recip_0, negate_0. reflexivity.
- apply (left_cancellation_ne_0 (.*.) (-x)).
  + apply (snd (flip_negate_ne_0 _)). trivial.
  + rewrite dec_recip_inverse.
    * rewrite negate_mult_negate. apply dec_recip_inverse. trivial.
    * apply (snd (flip_negate_ne_0 _)). trivial.
Qed.
End contents.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (/ _ <> 0)) =>
  eapply @dec_recip_ne_0 : typeclass_instances.

(* Given a decidable field we can easily construct a constructive field. *)
Section is_field.
  Context `{IsDecField F} `{Apart F} `{!TrivialApart F}
    `{Decidable.DecidablePaths F}.

  Global Instance recip_dec_field: Recip F := fun x => / x.1.

  Local Existing Instance dec_strong_setoid.

  Global Instance decfield_field : IsField F.
  Proof.
  split; try apply _.
  - apply (dec_strong_binary_morphism (+)).
  - apply (dec_strong_binary_morphism (.*.)).
  - intros [x Px]. rapply (dec_recip_inverse x).
    apply trivial_apart. trivial.
  Qed.

  Lemma dec_recip_correct (x : F) Px : / x = // (x;Px).
  Proof.
  apply (left_cancellation_ne_0 (.*.) x).
  - apply trivial_apart. trivial.
  - rewrite dec_recip_inverse, reciperse_alt by (apply trivial_apart;trivial).
    reflexivity.
  Qed.
End is_field.

(* Definition stdlib_field_theory F `{DecField F} :
  Field_theory.field_theory 0 1 (+) (.*.) (fun x y => x - y)
    (-) (fun x y => x / y) (/) (=).
Proof with auto.
  intros.
  constructor.
     apply (theory.rings.stdlib_ring_theory _).
    apply (is_ne_0 1).
   reflexivity.
  intros.
  rewrite commutativity. now apply dec_recip_inverse.
Qed. *)

(* Section from_stdlib_field_theory.
  Context `(ftheory : @field_theory F Fzero Fone Fplus Fmult Fminus Fnegate
    Fdiv Frecip Fe)
    (rinv_0 : Fe (Frecip Fzero) Fzero)
    `{!@Setoid F Fe}
    `{!Proper (Fe ==> Fe ==> Fe) Fplus}
    `{!Proper (Fe ==> Fe ==> Fe) Fmult}
    `{!Proper (Fe ==> Fe) Fnegate}
    `{!Proper (Fe ==> Fe) Frecip}.

  Add Field F2 : ftheory.

  Definition from_stdlib_field_theory: @DecField F Fe Fplus Fmult
    Fzero Fone Fnegate Frecip.
  Proof with auto.
   destruct ftheory.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, zero_is_mon_unit, plus_is_sg_op,
     one_is_mon_unit, mult_is_sg_op, plus, mult, recip, negate; try field.
   unfold recip, mult.
   simpl.
   assert (Fe (Fmult x (Frecip x)) (Fmult (Frecip x) x)) as E by ring.
   rewrite E.
  Qed.
End from_stdlib_field_theory. *)

Section morphisms.
  Context  `{IsDecField F} `{TrivialApart F} `{Decidable.DecidablePaths F}.

  Global Instance dec_field_to_domain_inj `{IsIntegralDomain R}
    `{!IsSemiRingPreserving (f : F -> R)} : IsInjective f.
  Proof.
  apply injective_preserves_0.
  intros x Efx.
  apply stable. intros Ex.
  destruct (is_ne_0 (1:R)).
  rewrite <-(rings.preserves_1 (f:=f)).
  rewrite <-(dec_recip_inverse x) by assumption.
  rewrite rings.preserves_mult, Efx.
  apply left_absorb.
  Qed.

  Lemma preserves_dec_recip `{IsDecField F2} `{forall x y: F2, Decidable (x = y)}
    `{!IsSemiRingPreserving (f : F -> F2)} x : f (/ x) = / f x.
  Proof.
  case (dec (x = 0)) as [E | E].
  - rewrite E, dec_recip_0, preserves_0, dec_recip_0. reflexivity.
  - intros.
    apply (left_cancellation_ne_0 (.*.) (f x)).
    + apply isinjective_ne_0. trivial.
    + rewrite <-preserves_mult, 2!dec_recip_inverse.
      * apply preserves_1.
      * apply isinjective_ne_0. trivial.
      * trivial.
  Qed.

  Lemma dec_recip_to_recip `{IsField F2} `{!IsSemiRingStrongPreserving (f : F -> F2)}
    x Pfx : f (/ x) = // (f x;Pfx).
  Proof.
  assert (x <> 0).
  - intros Ex.
    destruct (apart_ne (f x) 0 Pfx).
    rewrite Ex, (preserves_0 (f:=f)). reflexivity.
  - apply (left_cancellation_ne_0 (.*.) (f x)).
    + apply isinjective_ne_0. trivial.
    + rewrite <-preserves_mult, dec_recip_inverse, reciperse_alt by assumption.
      apply preserves_1.
  Qed.
End morphisms.
