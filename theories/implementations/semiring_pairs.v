Require Import HoTT.hit.quotient
  HoTT.Basics.PathGroupoids
  HoTT.Types.Universe
  HoTT.Basics.Trunc
  HoTT.Basics.Decidable
  HoTT.Types.Record
  HoTT.Types.Prod
  HoTT.Types.Arrow
  HoTT.Types.Sum
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

Definition SRle `{Le SR} : Le (SRpair SR)
  := fun a b => pos a + neg b <= pos b + neg a.
Definition SRlt `{Lt SR} : Lt (SRpair SR)
  := fun a b => pos a + neg b < pos b + neg a.
Definition SRapart `{Apart SR} : Apart (SRpair SR)
  := fun a b => apart (pos a + neg b) (pos b + neg a).

Global Instance SRle_hprop `{Le SR} `{is_mere_relation SR le}
  : is_mere_relation (SRpair SR) SRle.
Proof.
intros;unfold SRle;apply _.
Qed.

Global Instance SRlt_hprop `{Lt SR} `{is_mere_relation SR lt}
  : is_mere_relation (SRpair SR) SRlt.
Proof.
intros;unfold SRlt;apply _.
Qed.

Global Instance SRapart_hprop `{Apart SR} `{is_mere_relation SR apart}
  : is_mere_relation (SRpair SR) SRapart.
Proof.
intros;unfold SRlt;apply _.
Qed.

End contents.

Arguments equiv {_ _} _ _.
Arguments SRle {_ _ _} _ _.
Arguments SRlt {_ _ _} _ _.
Arguments SRapart {_ _ _} _ _.

Section with_srorder.

Context SR `{SemiRingOrder SR} `{∀ z, LeftCancellation (+) z}
  `{is_mere_relation SR le}.

Instance : SemiRing SR := srorder_semiring.

Lemma le_respects_aux : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRle q1 r1 -> SRle q2 r2.
Proof.
unfold equiv,SRle;intros [pa na] [pb nb] Eq [pc nc] [pd nd] Er E;simpl in *.
apply (order_reflecting (+ (pc + na))).
assert (Erw : pb + nd + (pc + na)
  = (pb + na) + (pc + nd)) by ring_with_nat.
rewrite Erw,<-Eq,Er;clear Erw.
assert (Erw : pa + nb + (pd + nc) = pd + nb + (pa + nc)) by ring_with_nat.
rewrite Erw.
apply (order_preserving _), E.
Qed.

Lemma le_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRle q1 r1 <~> SRle q2 r2.
Proof.
intros. apply equiv_iff_hprop_uncurried.
split;apply le_respects_aux;trivial;apply symmetry;trivial.
Qed.

End with_srorder.

Section with_strict_srorder.

Context SR `{StrictSemiRingOrder SR} `{∀ z, LeftCancellation (+) z}
  `{is_mere_relation SR lt}.

Instance : SemiRing SR := strict_srorder_semiring.

Lemma lt_respects_aux : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRlt q1 r1 -> SRlt q2 r2.
Proof.
unfold equiv,SRlt;intros [pa na] [pb nb] Eq [pc nc] [pd nd] Er E;simpl in *.
apply (strictly_order_reflecting (+ (pc + na))).
assert (Erw : pb + nd + (pc + na)
  = (pb + na) + (pc + nd)) by ring_with_nat.
rewrite Erw,<-Eq,Er;clear Erw.
assert (Erw : pa + nb + (pd + nc) = pd + nb + (pa + nc)) by ring_with_nat.
rewrite Erw.
apply (strictly_order_preserving _), E.
Qed.

Lemma lt_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRlt q1 r1 <~> SRlt q2 r2.
Proof.
intros. apply equiv_iff_hprop_uncurried.
split;apply lt_respects_aux;trivial;apply symmetry;trivial.
Qed.

End with_strict_srorder.

Section with_apart.
Context SR `{FullPseudoSemiRingOrder SR} `{IsHSet SR}.
Context `{∀ z, StrongLeftCancellation (+) z}.

Instance : IsApart SR := pseudo_order_apart.
Instance : SemiRing SR := pseudo_srorder_semiring.

Instance SRapart_cotrans : CoTransitive SRapart.
Proof.
hnf.
unfold SRapart. intros q1 q2 Eq r.
apply (strong_left_cancellation (+) (neg r)) in Eq.
apply (merely_destruct (cotransitive Eq (pos r + neg q1 + neg q2)));
intros [E|E];apply tr.
- left. apply (strong_extensionality (+ (neg q2))).
  assert (Hrw : pos q1 + neg r + neg q2
    = neg r + (pos q1 + neg q2)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  trivial.
- right. apply (strong_extensionality (+ (neg q1))).
  assert (Hrw : pos r + neg q2 + neg q1 = pos r + neg q1 + neg q2)
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pos q2 + neg r + neg q1 = neg r + (pos q2 + neg q1))
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  trivial.
Qed.

Instance : Symmetric SRapart.
Proof.
hnf.
unfold SRapart.
intros ??;apply symmetry.
Qed.

Lemma apart_respects_aux
  : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRapart q1 r1 -> SRapart q2 r2.
Proof.
assert (forall q1 q2, equiv q1 q2 -> forall r, SRapart q1 r -> SRapart q2 r)
  as E.
- intros q1 q2 Eq r Er.
  unfold SRapart,equiv in *.
  apply (strong_extensionality (+ (neg q1))).
  assert (Hrw : pos q2 + neg r + neg q1 = (pos q2 + neg q1) + neg r)
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  rewrite <-Eq.
  assert (Hrw : pos q1 + neg q2 + neg r = neg q2 + (pos q1 + neg r))
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pos r + neg q2 + neg q1 = neg q2 + (pos r + neg q1))
  by ring_with_nat;rewrite Hrw;clear Hrw.
  apply (strong_left_cancellation _ _),Er.
- intros ?? Eq ?? Er E'.
  apply E with q1;trivial.
  apply symmetry;apply E with r1;apply symmetry;trivial.
  apply symmetry;trivial.
Qed.

Lemma apart_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  SRapart q1 r1 <~> SRapart q2 r2.
Proof.
intros ?? Eq ?? Er.
apply equiv_iff_hprop_uncurried.
split;apply apart_respects_aux;trivial;apply symmetry;trivial.
Qed.

End with_apart.

End SRPair.
Import SRPair.

Module Completion.

Section contents.
Universe UR.
Context `{Funext} `{Univalence} (SR : Type@{UR}) `{SemiRing SR} `{IsHSet SR}.
Context `{∀ z, LeftCancellation (+) z}.

(* Add Ring SR : (rings.stdlib_semiring_theory SR). *)

Definition R := quotient equiv.

Global Instance class : Cast (SRpair SR) R := class_of _.

Global Instance SR_to_R : Cast SR R := compose class (SRpair_inject _).

Definition path {x y} : equiv x y -> class x = class y := related_classes_eq _.

Definition related_path {x y} : class x = class y -> equiv x y
  := classes_eq_related _ _ _.

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

Universe UR2.

Global Instance pl : Plus R.
Proof.
refine (R_rec2@{UR UR2 UR} (fun x y => class (SRPair.pl _ x y)) _).
intros;apply path;eapply pl_respects;trivial.
Defined.

Definition pl_compute q r : (class q) + (class r) = class (SRPair.pl _ q r)
  := 1.

Global Instance ml : Mult R.
Proof.
refine (R_rec2@{UR UR2 UR} (fun x y => class (SRPair.ml _ x y)) _).
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

Lemma R_ring' : Ring R.
Proof.
repeat split;try apply _;
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
  ring_with_nat.
- apply (R_ind _).
  intros;apply path;red;simpl.
  ring_with_nat.
- apply (R_ind _).
  intros;apply path;red;simpl.
  ring_with_nat.
- apply (R_ind2 _).
  intros;apply path;red;simpl.
  ring_with_nat.
- apply (R_ind3 _).
  intros [pa na] [pb nb] [pc nc];apply path;red;simpl.
  ring_with_nat.
Qed.

Global Instance R_ring : Ring R.
Proof.
exact R_ring'@{UR2 UR2 UR2 UR2 UR2 UR2 UR2}.
Qed.

(* A final word about inject *)
Lemma SR_to_R_morphism_aux : SemiRing_Morphism (cast SR R).
Proof.
(* This produces less universes. *)
pose proof R_ring.
repeat (constructor; try apply _).
- intros x y.
  apply path. red. simpl. ring_with_nat.
- intros x y. apply path. red;simpl.
  ring_with_nat.
Qed.

Global Instance SR_to_R_morphism
  : @SemiRing_Morphism _ _ _ _ _ _ pl ml _ _ (cast SR R).
Proof.
exact (SR_to_R_morphism_aux@{UR2 UR2 UR2 UR2}).
Qed.

Global Instance SR_to_R_injective : Injective (cast SR R).
Proof.
split.
intros x y E. apply related_path@{i i j} in E.
red in E. simpl in E. rewrite 2!plus_0_r in E. trivial.
Qed.

Lemma SRpair_splits' : forall n m : SR, class (C n m) = 'n + - 'm.
Proof.
intros.
apply path;red;simpl.
ring_with_nat.
Qed.

Lemma SRpair_splits : forall n m, class (C n m) = 'n + - 'm.
Proof.
exact SRpair_splits'@{UR2 UR2 UR2}.
Qed.

End contents.

Section with_semiring_order.
  Context `{Funext} `{Univalence} SR `{SemiRingOrder SR} `{IsHSet SR}
    `{is_mere_relation SR le}
    `{∀ z, LeftCancellation (+) z}.

  Instance : SemiRing SR := srorder_semiring.

  Notation R := (R SR).

  Definition Rle_hProp : R -> R -> hProp.
  Proof.
  apply (R_rec2 SR (fun q r => BuildhProp (SRle q r))).
  intros. apply path_hprop. simpl.
  apply (le_respects _);trivial.
  Defined.

  Global Instance Rle : Le R := fun x y => Rle_hProp x y.

  Lemma Rle_def : forall a b, class SR a <= class SR b = SRle a b.
  Proof. reflexivity. Qed.

  Instance: PartialOrder (le:Le R).
  Proof.
  split;[apply _|split|].
  - hnf. apply (R_ind _ _).
    intros. change (SRle x x). red. reflexivity.
  - hnf. apply (R_ind3 _ (fun _ _ _ => _ -> _ -> _)).
    intros [pa na] [pb nb] [pc nc]. rewrite !Rle_def. unfold SRle;simpl.
    intros E1 E2.
    apply (order_reflecting (+ (nb + pb))).
    assert (Hrw : pa + nc + (nb + pb) = (pa + nb) + (pb + nc)) by ring_with_nat.
    rewrite Hrw;clear Hrw.
    assert (Hrw : pc + na + (nb + pb) = (pb + na) + (pc + nb)) by ring_with_nat.
    rewrite Hrw;clear Hrw.
    apply plus_le_compat;trivial.
  - hnf. apply (R_ind2 _ (fun _ _ => _ -> _ -> _)).
    intros [pa na] [pb nb];rewrite !Rle_def;unfold SRle;simpl.
    intros E1 E2;apply path;red;simpl.
    apply (antisymmetry le);trivial.
  Qed.

  Global Instance: OrderEmbedding (cast SR R).
  Proof.
  repeat (split; try apply _).
  - intros. rewrite Rle_def. unfold SRle. simpl.
    rewrite 2!plus_0_r;trivial.
  - intros ??. rewrite Rle_def. unfold SRle. simpl.
    rewrite 2!plus_0_r;trivial.
  Qed.

  Instance: ∀ z : R, OrderPreserving ((+) z).
  Proof.
  intro z;repeat (split; try apply _).
  revert z.
  apply (R_ind3 _ (fun _ _ _ => _ -> _)).
  intros [pc nc] [pa na] [pb nb]. rewrite !Rle_def;unfold SRle;simpl.
  intros E.
  assert (Hrw : pc + pa + (nc + nb) = (pc + nc) + (pa + nb)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pc + pb + (nc + na) = (pc + nc) + (pb + na)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  apply (order_preserving _),E.
  Qed.

  Instance: ∀ x y : R, PropHolds (0 ≤ x) → PropHolds (0 ≤ y) →
    PropHolds (0 ≤ x * y).
  Proof.
  unfold PropHolds.
  apply (R_ind2 _ (fun _ _ => _ -> _ -> _)).
  intros [pa na] [pb nb]. rewrite !Rle_def;unfold SRle;simpl.
  rewrite !plus_0_l,!plus_0_r.
  intros E1 E2.
  destruct (decompose_le E1) as [a [Ea1 Ea2]], (decompose_le E2) as [b [Eb1 Eb2]].
  rewrite Ea2, Eb2.
  apply compose_le with (a * b).
  - apply nonneg_mult_compat;trivial.
  - ring_with_nat.
  Qed.

  Global Instance: SemiRingOrder (le : Le R).
  Proof. apply rings.from_ring_order; apply _. Qed.

  Global Instance Rle_dec `{forall x y : SR, Decidable (x <= y)}
    : forall x y : R, Decidable (x <= y).
  Proof.
  apply (R_ind2 _ _).
  intros a b;rewrite Rle_def.
  unfold SRle. apply _.
  Qed.

End with_semiring_order.

Section with_strict_semiring_order.
  Context `{Funext} `{Univalence} SR `{StrictSemiRingOrder SR} `{IsHSet SR}
    `{is_mere_relation SR lt}
    `{∀ z, LeftCancellation (+) z}.

  Instance : SemiRing SR := strict_srorder_semiring.

  Notation R := (R SR).

  Definition Rlt_hProp : R -> R -> hProp.
  Proof.
  apply (R_rec2 SR (fun q r => BuildhProp (SRlt q r))).
  intros. apply path_hprop. simpl.
  apply (lt_respects _);trivial.
  Defined.

  Global Instance Rlt : Lt R := fun x y => Rlt_hProp x y.

  Lemma Rlt_def : forall a b, class SR a < class SR b = SRlt a b.
  Proof. reflexivity. Qed.

  Instance: StrictOrder (lt:Lt R).
  Proof.
  split.
  - apply _.
  - (* we need to change so that it sees Empty,
       needed to figure out IsHProp (using Funext) *)
    change (forall x, x < x -> Empty). apply (R_ind _ (fun _ => _ -> _)).
    intros [pa na];rewrite Rlt_def;unfold SRlt;simpl.
    apply irreflexivity,_.
  - hnf. apply (R_ind3 _ (fun _ _ _ => _ -> _ -> _)).
    intros [pa na] [pb nb] [pc nc];rewrite !Rlt_def;unfold SRlt;simpl.
    intros E1 E2.
    apply (strictly_order_reflecting (+ (nb + pb))).
    assert (Hrw : pa + nc + (nb + pb) = (pa + nb) + (pb + nc)) by ring_with_nat.
    rewrite Hrw;clear Hrw.
    assert (Hrw : pc + na + (nb + pb) = (pb + na) + (pc + nb)) by ring_with_nat.
    rewrite Hrw;clear Hrw.
    apply plus_lt_compat;trivial.
  Qed.

  Instance plus_strict_order_preserving_l
    : ∀ z : R, StrictlyOrderPreserving ((+) z).
  Proof.
  intros z;split;[split;apply _|].
  revert z.
  apply (R_ind3 _ (fun _ _ _ => _ -> _)).
  intros [pa na] [pb nb] [pc nc].
  rewrite !Rlt_def;unfold SRlt;simpl.
  intros E.
  assert (Hrw : pa + pb + (na + nc) = (pa + na) + (pb + nc)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pa + pc + (na + nb) = (pa + na) + (pc + nb)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  apply (strictly_order_preserving _),E.
  Qed.

  Instance: ∀ x y : R, PropHolds (0 < x) → PropHolds (0 < y) →
    PropHolds (0 < x * y).
  Proof.
  unfold PropHolds.
  apply (R_ind2 _ (fun _ _ => _ -> _ -> _)).
  intros [pa na] [pb nb]. rewrite !Rlt_def;unfold SRlt;simpl.
  rewrite !plus_0_l,!plus_0_r.
  intros E1 E2.
  destruct (decompose_lt E1) as [a [Ea1 Ea2]], (decompose_lt E2) as [b [Eb1 Eb2]].
  rewrite Ea2, Eb2.
  apply compose_lt with (a * b).
  - apply pos_mult_compat;trivial.
  - ring_with_nat.
  Qed.

  Global Instance R_strict_srorder : StrictSemiRingOrder (lt:Lt R).
  Proof. apply from_strict_ring_order; apply _. Qed.

  Global Instance Rlt_dec `{forall x y : SR, Decidable (x < y)}
    : forall x y : R, Decidable (x < y).
  Proof.
  apply (R_ind2 _ _).
  intros a b;rewrite Rlt_def;unfold SRlt.
  apply _.
  Qed.
End with_strict_semiring_order.

Section with_full_pseudo_semiring_order.
  Context `{Funext} `{Univalence} SR `{FullPseudoSemiRingOrder SR} `{IsHSet SR}
    `{is_mere_relation SR le} `{is_mere_relation SR lt}
    `{∀ z, LeftCancellation (+) z}.

  Instance: IsApart SR := pseudo_order_apart.
  Instance: SemiRing SR := pseudo_srorder_semiring.

  Notation R := (R SR).

  Definition Rapart_hProp : R -> R -> hProp.
  Proof.
  apply (R_rec2 SR (fun q r => BuildhProp (SRapart q r))).
  intros. apply path_hprop. simpl.
  apply (apart_respects _);trivial.
  Defined.

  Global Instance Rapart : Apart R := fun x y => Rapart_hProp x y.

  Lemma Rapart_def : forall a b, apart (class SR a) (class SR b) = SRapart a b.
  Proof. reflexivity. Qed.

  Global Instance SRpair_trivial_apart `{!TrivialApart SR}
    : TrivialApart R.
  Proof.
  split;try apply _.
  apply (R_ind2 _ _).
  intros [pa na] [pb nb];rewrite Rapart_def;unfold SRapart;simpl.
  split;intros E1.
  - intros E2. apply (related_path SR) in E2.
    red in E2;simpl in E2.
    apply trivial_apart in E1. auto.
  - apply trivial_apart. intros E2.
    apply E1,path. red;simpl. trivial.
  Qed.

  Instance: IsApart R.
  Proof.
  split.
  - apply _.
  - apply _.
  - hnf. apply (R_ind2 _ (fun _ _ => _ -> _)).
    intros [pa na] [pb nb];rewrite !Rapart_def;unfold SRapart;simpl.
    apply symmetry.
  - hnf. intros x y E z;revert x y z E.
    apply (R_ind3 _ (fun _ _ _ => _ -> _)).
    intros a b c;rewrite !Rapart_def;unfold SRapart;simpl.
    intros E1.
    apply (strong_left_cancellation (+) (neg c)) in E1.
    eapply (merely_destruct (cotransitive E1 _));intros [E2|E2];apply tr.
    + left. apply (strong_extensionality (+ (neg b))).
      assert (Hrw : pos a + neg c + neg b = neg c + (pos a + neg b))
      by ring_with_nat;rewrite Hrw;exact E2.
    + right. apply (strong_extensionality (+ (neg a))).
      assert (Hrw : pos c + neg b + neg a = pos c + neg a + neg b)
      by ring_with_nat;rewrite Hrw;clear Hrw.
      assert (Hrw : pos b + neg c + neg a = neg c + (pos b + neg a))
      by ring_with_nat;rewrite Hrw;clear Hrw.
      trivial.
  - apply (R_ind2 _ _).
    intros a b;rewrite Rapart_def;unfold SRapart.
    split;intros E.
    + apply path;red.
      apply tight_apart,E.
    + apply (related_path _) in E. apply tight_apart,E.
  Qed.

  Instance: FullPseudoOrder (le:Le R) (lt:Lt R).
  Proof.
  split;[split;try apply _|].
  - apply (R_ind2 _ _).
    intros a b;rewrite !Rlt_def;unfold SRlt.
    apply pseudo_order_antisym.
  - hnf. intros a b E c;revert a b c E.
    apply (R_ind3 _ (fun _ _ _ => _ -> _)).
    intros a b c;rewrite !Rlt_def;unfold SRlt.
    intros E1.
    apply (strictly_order_preserving (+ neg c)) in E1.
    eapply (merely_destruct (cotransitive E1 _));intros [E2|E2];apply tr.
    + left. apply (strictly_order_reflecting ((neg b) +)).
      assert (Hrw : neg b + (pos a + neg c) = pos a + neg b + neg c)
      by ring_with_nat;rewrite Hrw;exact E2.
    + right. apply (strictly_order_reflecting ((neg a) +)).
      assert (Hrw : neg a + (pos c + neg b) = neg b + (pos c + neg a))
      by ring_with_nat;rewrite Hrw;clear Hrw.
      assert (Hrw : neg a + (pos b + neg c) = pos b + neg a + neg c)
      by ring_with_nat;rewrite Hrw;clear Hrw.
      trivial.
  - apply (@R_ind2 _).
    + intros a b.
      apply @trunc_prod;[|apply _].
      apply (@trunc_arrow _).
      apply ishprop_sum;try apply _.
      intros E1 E2;apply (irreflexivity lt a).
      transitivity b;trivial.
    + intros a b;rewrite Rapart_def,!Rlt_def;unfold SRapart,SRlt.
      apply apart_iff_total_lt.
  - apply (R_ind2 _ _).
    intros a b;rewrite Rle_def,Rlt_def;unfold SRlt,SRle.
    apply le_iff_not_lt_flip.
  Qed.

  Instance: ∀ z : R, StrongMorphism (z *.).
  Proof.
  intros z;split;try apply _.
  revert z;apply (R_ind3 _ (fun _ _ _ => _ -> _)).
  intros [zp zn] [xp xn] [yp yn];rewrite !Rapart_def;unfold SRapart;simpl.
  intros E1.
  refine (merely_destruct (strong_binary_extensionality (+)
       (zp * (xp + yn)) (zn * (yp + xn)) (zp * (yp + xn)) (zn * (xp + yn)) _) _).
  - assert (Hrw : zp * (xp + yn) + zn * (yp + xn)
    = zp * xp + zn * xn + (zp * yn + zn * yp))
    by ring_with_nat;rewrite Hrw;clear Hrw.
    assert (Hrw : zp * (yp + xn) + zn * (xp + yn)
    = zp * yp + zn * yn + (zp * xn + zn * xp))
    by ring_with_nat;rewrite Hrw;exact E1.
  - intros [E2|E2].
    + apply (strong_extensionality (zp *.)).
      trivial.
    + apply symmetry;apply (strong_extensionality (zn *.)).
      trivial.
  Qed.

  Global Instance R_full_pseudo_srorder
    : FullPseudoSemiRingOrder (le:Le R) (lt:Lt R).
  Proof.
  apply from_full_pseudo_ring_order; try apply _.
  - (* Fail refine (plus_strict_order_preserving_l _ ). *)
    (* This appears to be a problem because the operations
       in the quotient depend on the proof that SR is a strictsemiringorder
       and this is proven in different ways in the goal and the lemma
       (with QED being opaque).
       Not sure if setting some QEDs to Defined would work. *)
    intros z;split;[split;apply _|].
    revert z.
    apply (R_ind3 _ (fun _ _ _ => _ -> _)).
    intros [pa na] [pb nb] [pc nc].
    rewrite !Rlt_def;unfold SRlt;simpl.
    intros E.
    assert (Hrw : pa + pb + (na + nc) = (pa + na) + (pb + nc)) by ring_with_nat.
    rewrite Hrw;clear Hrw.
    assert (Hrw : pa + pc + (na + nb) = (pa + na) + (pc + nb)) by ring_with_nat.
    rewrite Hrw;clear Hrw.
    apply (strictly_order_preserving _),E.
  - apply apartness.strong_binary_setoid_morphism_commutative.
  - (* same problem as bullet one *)
    unfold PropHolds.
    apply (R_ind2 _ (fun _ _ => _ -> _ -> _)).
    intros [pa na] [pb nb]. rewrite !Rlt_def;unfold SRlt;simpl.
    rewrite !plus_0_l,!plus_0_r.
    intros E1 E2.
    destruct (decompose_lt E1) as [a [Ea1 Ea2]], (decompose_lt E2) as [b [Eb1 Eb2]].
    rewrite Ea2, Eb2.
    apply compose_lt with (a * b).
    + apply pos_mult_compat;trivial.
    + ring_with_nat.
  Qed.
End with_full_pseudo_semiring_order.

(* Not sure if this does anything since we go through quotient but oh well *)
Typeclasses Opaque Rle.

End Completion.
