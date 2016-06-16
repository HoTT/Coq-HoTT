Require Import HoTT.hit.quotient
  HoTT.Basics.PathGroupoids
  HoTT.Types.Universe
  HoTT.Basics.Trunc
  HoTT.Basics.Decidable
  HoTT.Types.Record
  HoTT.TruncType.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.theory.rings
  HoTTClasses.orders.rings
  HoTTClasses.tactics.ring_tac
  HoTTClasses.interfaces.naturals
  HoTTClasses.implementations.peano_naturals.

Module SRPair.

Record SRpair (SR : Type) := C { pos : SR ; neg : SR }.
Arguments C {SR} _ _.
Arguments pos {SR} _.
Arguments neg {SR} _.

Section contents.
Context SR `{SemiRing SR} `{IsHSet SR}.
Context `{∀ z, LeftCancellation (+) z}.

Global Instance: IsHSet (SRpair SR).
Proof.
assert (E : sigT (fun _ : SR => SR) <~> (SRpair SR)).
- issig (@C SR) (@pos SR) (@neg SR).
- apply (trunc_equiv' _ E).
Qed.

Global Instance SRpair_inject : Cast SR (SRpair SR) := fun x => C x 0.

Definition equiv := fun x y => pos x + neg y = pos y + neg x.

Global Instance: Equivalence equiv.
Proof.
split.
- hnf. reflexivity.
- hnf. unfold equiv.
  intros ??;apply symmetry.
- hnf. unfold equiv.
  intros a b c E1 E2.
  apply (left_cancellation (+) (neg b)).
  rewrite (plus_assoc (neg b) (pos a)).
  rewrite (plus_comm (neg b) (pos a)), E1.
  rewrite (plus_comm (pos b)). rewrite <-plus_assoc.
  rewrite E2. rewrite (plus_comm (pos c) (neg b)).
  rewrite plus_assoc. rewrite (plus_comm (neg a)).
  rewrite <-plus_assoc. rewrite (plus_comm (neg a)).
  reflexivity.
Qed.

Instance pl : Plus (SRpair SR) := fun x y => C (pos x + pos y) (neg x + neg y).

Instance ml : Mult (SRpair SR) := fun x y =>
  C (pos x * pos y + neg x * neg y) (pos x * neg y + neg x * pos y).

Instance opp : Negate (SRpair SR) := fun x => C (neg x) (pos x).

Instance SR0 : Zero (SRpair SR) := C 0 0.

Instance SR1 : One (SRpair SR) := C 1 1.

Lemma pl_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  equiv (q1 + r1) (q2 + r2).
Proof.
unfold equiv;simpl.
intros q1 q2 Eq r1 r2 Er.
rewrite (plus_assoc _ (neg q2)).
rewrite <-(plus_assoc (pos q1)).
rewrite (plus_comm (pos r1)).
rewrite (plus_assoc (pos q1)). rewrite Eq.
rewrite <-(plus_assoc _ (pos r1)). rewrite Er.
rewrite plus_assoc. rewrite <-(plus_assoc (pos q2)).
rewrite (plus_comm (neg q1)). rewrite !plus_assoc.
reflexivity.
Qed.

Lemma ml_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  equiv (q1 * r1) (q2 * r2).
Proof.
intros q1 q2 Eq r1 r2 Er. transitivity (q1 * r2);unfold equiv in *;simpl.
- transitivity (pos q1 * (pos r1 + neg r2) + neg q1 * (neg r1 + pos r2)).
  + rewrite 2!plus_mult_distr_l.
    rewrite <-2!plus_assoc.
    apply ap.
    rewrite 2!plus_assoc. rewrite (plus_comm (neg q1 * neg r1)).
    reflexivity.
  + rewrite Er. rewrite plus_mult_distr_l.
    rewrite (plus_comm (neg r1)).
    rewrite <-Er. rewrite plus_mult_distr_l.
    rewrite <-2!plus_assoc. apply ap.
    rewrite (plus_comm (neg q1 * pos r1)).
    rewrite 2!plus_assoc.
    rewrite (plus_comm (pos q1 * neg r1)). reflexivity.
- transitivity ((pos q1 + neg q2) * pos r2 + (neg q1 + pos q2) * neg r2).
  + rewrite 2!plus_mult_distr_r.
    rewrite <-2!plus_assoc;apply ap.
    rewrite (plus_comm (pos q2 * neg r2)).
    rewrite 2!plus_assoc. rewrite (plus_comm (neg q1 * neg r2)).
    reflexivity.
  + rewrite Eq,plus_mult_distr_r.
    rewrite (plus_comm (neg q1)),<-Eq,plus_mult_distr_r.
    rewrite <-2!plus_assoc. apply ap.
    rewrite plus_assoc,(plus_comm (neg q1 * pos r2)).
    apply plus_comm.
Qed.

Lemma opp_respects : forall q1 q2, equiv q1 q2 -> equiv (opp q1) (opp q2).
Proof.
unfold equiv;simpl.
intros q1 q2 E.
rewrite !(plus_comm (neg _)). symmetry. apply E.
Qed.

End contents.

Arguments equiv {_ _} _ _.

(* Section with_apart.
Context SR `{SemiRing SR} `{Apart SR} `{!IsApart SR} `{IsHSet SR}.
Context `{∀ z, LeftCancellation (+) z}.

Instance: CoTransitive SRapart.
Proof.
hnf.
unfold SRapart. intros q1 q2 Eq r.
apply (strong_left_cancellation (+) (neg r)) in Eq.
Qed.

Lemma apart_respects_aux
  : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRapart q1 r1 -> SRapart q2 r2.
Proof.
assert (forall q1 q2, equiv q1 q2 -> forall r, SRapart q1 r -> SRapart q2 r)
  as E.
- intros q1 q2 Eq r Er.
  unfold SRapart,equiv in *.
  destruct (cotransitive Er (pos r + neg q2)).
Qed.

Lemma apart_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRapart q1 r1 <~> SRapart q2 r2.
Proof.
intros ?? Eq ?? Er.
unfold SRapart.
apply equiv_iff_hprop_uncurried.
Qed.

End with_apart. *)

End SRPair.
Import SRPair.

Section contents.
Context `{Funext} `{Univalence} SR `{SemiRing SR} `{IsApart SR} `{IsHSet SR}.
Context `{∀ z, LeftCancellation (+) z}.

(* Add Ring SR : (rings.stdlib_semiring_theory SR). *)

Definition R := quotient equiv.

Global Instance class : Cast (SRpair SR) R := class_of _.

Global Instance: Cast SR R := compose class (SRpair_inject _).

Definition path {x y} : equiv x y -> class x = class y := related_classes_eq _.

Definition R_rect (P : R -> Type) {sP : forall x, IsHSet (P x)}
  (dclass : forall x, P (class x))
  (dequiv : forall x y E, (path E) # (dclass x) = (dclass y))
  : forall q, P q
  := quotient_ind equiv P dclass dequiv.

Definition R_compute P {sP} dclass dequiv x
 : @R_rect P sP dclass dequiv (class x) = dclass x := 1.

Definition R_compute_path P {sP} dclass dequiv q r (E : equiv q r)
  : apD (@R_rect P sP dclass dequiv) (path E) = dequiv q r E
  := quotient_ind_compute_path _ _ _ _ _ _ _ _.

Definition R_ind (P : R -> Type) {sP : forall x, IsHProp (P x)}
  (dclass : forall x, P (class x)) : forall x, P x.
Proof.
apply (R_rect P dclass).
intros;apply path_ishprop.
Qed.

Definition R_ind2 (P : R -> R -> Type) {sP : forall x y, IsHProp (P x y)}
  (dclass : forall x y, P (class x) (class y)) : forall x y, P x y.
Proof.
apply (R_ind (fun x => forall y, _));intros x.
apply (R_ind _);intros y.
apply dclass.
Qed.

Definition R_ind3 (P : R -> R -> R -> Type) {sP : forall x y z, IsHProp (P x y z)}
  (dclass : forall x y z, P (class x) (class y) (class z)) : forall x y z, P x y z.
Proof.
apply (R_ind (fun x => forall y z, _));intros x.
apply (R_ind2 _). auto.
Qed.

Definition R_rec {T : Type} {sT : IsHSet T}
  : forall (dclass : SRpair SR -> T)
  (dequiv : forall x y, equiv x y -> dclass x = dclass y),
  R -> T
  := quotient_rec equiv.

Definition R_rec_compute T sT dclass dequiv x
  : @R_rec T sT dclass dequiv (class x) = dclass x
  := 1.

Definition R_rec2 {T} {sT : IsHSet T}
  : forall (dclass : SRpair SR -> SRpair SR -> T)
  (dequiv : forall x1 x2, equiv x1 x2 -> forall y1 y2, equiv y1 y2 ->
    dclass x1 y1 = dclass x2 y2),
  R -> R -> T
  := @quotient_rec2 _ _ _ _ _ (BuildhSet _).

Definition R_rec2_compute {T sT} dclass dequiv x y
  : @R_rec2 T sT dclass dequiv (class x) (class y) = dclass x y
  := 1.

Lemma dec_class `{DecidablePaths SR} : forall q r, Decidable (class q = class r).
Proof.
intros q r.
destruct (decide (equiv q r)) as [E|E].
- left. apply path,E.
- right. intros E'.
  apply E. apply (classes_eq_related _ _ _ E').
Defined.

Global Instance R_dec `{DecidablePaths SR}
  : DecidablePaths R.
Proof.
hnf. apply (R_ind2 _).
apply dec_class.
Defined.


(* Relations, operations and constants *)

Global Instance z : Zero R := (' 0 : R).
Global Instance u : One R := (' 1 : R).

Global Instance pl : Plus R.
Proof.
refine (R_rec2 (fun x y => class (SRPair.pl _ x y)) _).
intros;apply path;eapply pl_respects;trivial.
Defined.

Definition pl_compute q r : (class q) + (class r) = class (SRPair.pl _ q r)
  := 1.

Global Instance ml : Mult R.
Proof.
refine (R_rec2 (fun x y => class (SRPair.ml _ x y)) _).
intros;apply path;eapply ml_respects;trivial.
Defined.

Definition ml_compute q r : (class q) * (class r) = class (SRPair.ml _ q r)
  := 1.

Global Instance opp : Negate R.
Proof.
red. apply (R_rec (fun x => class (SRPair.opp _ x))).
intros;apply path;eapply opp_respects;trivial.
Defined.

Definition opp_compute q : - (class q) = class (SRPair.opp _ q)
  := 1.

Global Instance: Ring R.
Proof.
repeat split;
first [change sg_op with mult; change mon_unit with 1|
       change sg_op with plus; change mon_unit with 0];hnf.
- apply (R_ind3 _).
  intros a b c;apply path;red;simpl.
  rewrite !plus_assoc. reflexivity.
- apply (R_ind _).
  intros a;apply path;red;simpl.
  rewrite !plus_0_l. reflexivity.
- apply (R_ind _).
  intros a;apply path;red;simpl.
  rewrite !plus_0_r. reflexivity.
- apply (R_ind _).
  intros a;apply path;red;simpl.
  rewrite plus_0_l,plus_0_r. apply plus_comm.
- apply (R_ind _).
  intros a;apply path;red;simpl.
  rewrite plus_0_l,plus_0_r. apply plus_comm.
- apply (R_ind2 _).
  intros a b;apply path;red;simpl.
  apply ap2;apply plus_comm.
- apply (R_ind3 _).
  intros [pa na] [pb nb] [pc nc];apply path;red;simpl.
  
Abort.
End contents.
(* 
Qed.

(* A final word about inject *)
Global Instance: SemiRing_Morphism SRpair_inject.
Proof.
  repeat (constructor; try apply _); try reflexivity.
   intros x y. change (x + y + (0 + 0) = x + y + 0). ring.
  intros x y. change (x * y + (x * 0 + 0 * y) = x * y + 0 * 0 + 0). ring.
Qed.

Global Instance: Injective SRpair_inject.
Proof.
  repeat (constructor; try apply _).
  intros x y. unfolds. now rewrite 2!rings.plus_0_r.
Qed.

Lemma SRpair_splits n m : C n m = 'n + -'m.
Proof. ring_on_sr. Qed.

Global Instance SRpair_le `{Le SR} : Le (SRpair SR)
  := λ x y, pos x + neg y ≤ pos y + neg x.
Global Instance SRpair_lt `{Lt SR} : Lt (SRpair SR)
  := λ x y, pos x + neg y < pos y + neg x.
Ltac unfold_le := unfold le, SRpair_le, equiv, SRpair_equiv; simpl.
Ltac unfold_lt := unfold lt, SRpair_lt, equiv, SRpair_equiv; simpl.

Section with_semiring_order.
  Context `{!SemiRingOrder SRle}.

  Instance: Proper ((=) ==> (=) ==> iff) SRpair_le.
  Proof.
    assert (∀ x1 y1 : SRpair SR, x1 = y1 →
            ∀ x2 y2, x2 = y2 → x1 ≤ x2 → y1 ≤ y2) as E.
     unfold_le. intros [xp1 xn1] [yp1 yn1] E1 [xp2 xn2] [yp2 yn2] E2 F. simpl in *.
     apply (order_reflecting (+ (xp2 + xn1))).
     setoid_replace (yp1 + yn2 + (xp2 + xn1)) with ((yp1 + xn1) + (xp2 + yn2))
      by ring.
     rewrite <-E1, E2.
     setoid_replace (xp1 + yn1 + (yp2 + xn2)) with ((yp2 + yn1) + (xp1 + xn2))
      by ring.
     now apply (order_preserving _).
    split; repeat intro; eapply E; eauto; symmetry; eauto.
  Qed.

  Instance: Reflexive SRpair_le.
  Proof. intros [? ?]. unfold_le. reflexivity. Qed.

  Instance: Transitive SRpair_le.
  Proof.
    intros [xp xn] [yp yn] [zp zn] E1 E2.
    unfold SRpair_le in *. simpl in *.
    apply (order_reflecting (+ (yn + yp))).
    setoid_replace (xp + zn + (yn + yp)) with ((xp + yn) + (yp + zn)) by ring.
    setoid_replace (zp + xn + (yn + yp)) with ((yp + xn) + (zp + yn)) by ring.
    now apply plus_le_compat.
  Qed.

  Instance: AntiSymmetric SRpair_le.
  Proof.
    intros [xp xn] [yp yn] E1 E2. unfold_le.
    now apply (antisymmetry (≤)).
  Qed.

  Instance: PartialOrder SRpair_le.
  Proof. repeat (split; try apply _). Qed.

  Global Instance: OrderEmbedding SRpair_inject.
  Proof.
    repeat (split; try apply _).
     intros x y E. unfold_le. simpl. now rewrite 2!rings.plus_0_r.
    intros x y E. unfold le, SRpair_le in E. simpl in E.
      now rewrite 2!rings.plus_0_r in E.
  Qed.

  Instance: ∀ z : SRpair SR, OrderPreserving ((+) z).
  Proof.
    repeat (split; try apply _). unfold_le.
    destruct z as [zp zn]. intros [xp xn] [yp yn] E. simpl in *.
    setoid_replace (zp + xp + (zn + yn)) with ((zp + zn) + (xp + yn)) by ring.
    setoid_replace (zp + yp + (zn + xn)) with ((zp + zn) + (yp + xn)) by ring.
    now apply (order_preserving _).
  Qed.

  Instance: ∀ x y : SRpair SR, PropHolds (0 ≤ x) → PropHolds (0 ≤ y) →
    PropHolds (0 ≤ x * y).
  Proof.
    intros [xp xn] [yp yn].
    unfold PropHolds. unfold_le. intros E1 E2.
    ring_simplify in E1. ring_simplify in E2.
    destruct (decompose_le E1) as [a [Ea1 Ea2]], (decompose_le E2) as [b [Eb1 Eb2]].
    rewrite Ea2, Eb2. ring_simplify.
    apply compose_le with (a * b).
     now apply nonneg_mult_compat.
    ring.
  Qed.

  Global Instance: SemiRingOrder SRpair_le.
  Proof. apply rings.from_ring_order; apply _. Qed.
End with_semiring_order.

Section with_strict_semiring_order.
  Context `{!StrictSemiRingOrder SRle}.

  Instance: Proper ((=) ==> (=) ==> iff) SRpair_lt.
  Proof.
    assert (∀ x1 y1 : SRpair SR, x1 = y1 →
            ∀ x2 y2, x2 = y2 → x1 < x2 → y1 < y2) as E.
     unfold_lt. intros [xp1 xn1] [yp1 yn1] E1 [xp2 xn2] [yp2 yn2] E2 F. simpl in *.
     apply (strictly_order_reflecting (+ (xp2 + xn1))).
     setoid_replace (yp1 + yn2 + (xp2 + xn1)) with ((yp1 + xn1) + (xp2 + yn2))
      by ring.
     rewrite <-E1, E2.
     setoid_replace (xp1 + yn1 + (yp2 + xn2)) with ((yp2 + yn1) + (xp1 + xn2))
      by ring.
     now apply (strictly_order_preserving _).
    split; repeat intro; eapply E; eauto; symmetry; eauto.
  Qed.

  Instance: Irreflexive SRpair_lt.
  Proof. intros [? ?] E. edestruct (irreflexivity (<)); eauto. Qed.

  Instance: Transitive SRpair_lt.
  Proof.
    intros [xp xn] [yp yn] [zp zn] E1 E2.
    unfold SRpair_lt in *. simpl in *.
    apply (strictly_order_reflecting (+ (yn + yp))).
    setoid_replace (xp + zn + (yn + yp)) with ((xp + yn) + (yp + zn)) by ring.
    setoid_replace (zp + xn + (yn + yp)) with ((yp + xn) + (zp + yn)) by ring.
    now apply plus_lt_compat.
  Qed.

  Instance: ∀ z : SRpair SR, StrictlyOrderPreserving ((+) z).
  Proof.
    repeat (split; try apply _). unfold_lt.
    destruct z as [zp zn]. intros [xp xn] [yp yn] E. simpl in *.
    setoid_replace (zp + xp + (zn + yn)) with ((zp + zn) + (xp + yn)) by ring.
    setoid_replace (zp + yp + (zn + xn)) with ((zp + zn) + (yp + xn)) by ring.
    now apply (strictly_order_preserving _).
  Qed.

  Instance: StrictSetoidOrder SRpair_lt.
  Proof. repeat (split; try apply _). Qed.

  Instance: ∀ x y : SRpair SR, PropHolds (0 < x) → PropHolds (0 < y) →
    PropHolds (0 < x * y).
  Proof.
    intros [xp xn] [yp yn].
    unfold PropHolds. unfold_lt. intros E1 E2.
    ring_simplify in E1. ring_simplify in E2.
    destruct (decompose_lt E1) as [a [Ea1 Ea2]], (decompose_lt E2) as [b [Eb1 Eb2]].
    rewrite Ea2, Eb2. ring_simplify.
    apply compose_lt with (a * b).
     now apply pos_mult_compat.
    ring.
  Qed.

  Global Instance: StrictSemiRingOrder SRpair_lt.
  Proof. apply from_strict_ring_order; apply _. Qed.
End with_strict_semiring_order.

Section with_full_pseudo_semiring_order.
  Context `{!FullPseudoSemiRingOrder SRle SRlt}.

  Instance: StrongSetoid SR := pseudo_order_setoid.




Global Instance SRpair_trivial_apart `{!TrivialApart SR}
  : TrivialApart (SRpair SR).
Proof. intros x y. now rapply trivial_apart. Qed.

  Instance: StrongSetoid (SRpair SR).
  Proof.
    split.
       intros [??] E. now eapply (irreflexivity (≶)); eauto.
      intros [??] [??] E. unfold apart, SRpair_apart. now symmetry.
     intros [xp xn] [yp yn] E [zp zn]. unfold apart, SRpair_apart in *. simpl in *.
     apply (strong_left_cancellation (+) zn) in E.
     edestruct (cotransitive E).
      left. apply (strong_extensionality (+ yn)).
      setoid_replace (xp + zn + yn) with (zn + (xp + yn)) by ring. eassumption.
     right. apply (strong_extensionality (+ xn)).
     setoid_replace (zp + yn + xn) with (zp + xn + yn) by ring.
     setoid_replace (yp + zn + xn) with (zn + (yp + xn)) by ring.
     eassumption.
    intros [??] [??]. now rapply tight_apart.
  Qed.

  Instance: FullPseudoOrder SRpair_le SRpair_lt.
  Proof.
    split.
     split; try apply _.
       intros [??] [??]. unfold_lt. now apply pseudo_order_antisym.
      intros [xp xn] [yp yn] E [zp zn]. unfold lt, SRpair_lt in *. simpl in *.
      apply (strictly_order_preserving (zn +)) in E.
      edestruct (cotransitive E).
       left. apply (strictly_order_reflecting (+ yn)).
       setoid_replace (xp + zn + yn) with (zn + (xp + yn)) by ring. eassumption.
      right. apply (strictly_order_reflecting (+ xn)).
      setoid_replace (zp + yn + xn) with (zp + xn + yn) by ring.
      setoid_replace (yp + zn + xn) with (zn + (yp + xn)) by ring.
      eassumption.
     intros [??] [??]. now rapply apart_iff_total_lt.
    intros [??] [??]. now rapply le_iff_not_lt_flip.
  Qed.

  Instance: ∀ z : SRpair SR, StrongSetoid_Morphism (z *.).
  Proof.
    intros [zp zn]. split; try apply _. intros [xp xn] [yp yn] E1.
    unfold apart, SRpair_apart in *. simpl in *.
    destruct (strong_binary_extensionality (+)
       (zp * (xp + yn)) (zn * (yp + xn)) (zp * (yp + xn)) (zn * (xp + yn))).
      eapply strong_setoids.apart_proper; eauto; ring.
     now apply (strong_extensionality (zp *.)).
    symmetry. now apply (strong_extensionality (zn *.)).
  Qed.

  Global Instance: FullPseudoSemiRingOrder SRpair_le SRpair_lt.
  Proof.
    apply from_full_pseudo_ring_order; try apply _.
    now apply strong_setoids.strong_binary_setoid_morphism_commutative.
  Qed.
End with_full_pseudo_semiring_order.

Global Instance SRpair_dec `{∀ x y : SR, Decision (x = y)}
  : ∀ x y : SRpair SR, Decision (x = y)
  := λ x y, decide_rel (=) (pos x + neg y) (pos y + neg x).

Global Program Instance SRpair_le_dec `{Le SR} `{∀ x y: SR, Decision (x ≤ y)}
  : ∀ x y : SRpair SR, Decision (x ≤ y) := λ x y,
  match decide_rel (≤) (pos x + neg y) (pos y + neg x) with
  | left E => left _
  | right E => right _
  end.

End semiring_pairs.

Typeclasses Opaque SRpair_equiv.
Typeclasses Opaque SRpair_le.
 *)