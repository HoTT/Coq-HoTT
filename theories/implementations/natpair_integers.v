(* The standard library's implementation of the integers (BinInt)
  uses nasty binary positive crap with various horrible horrible bit fiddling
  operations on it (especially Pminus).
  The following is a much simpler implementation whose correctness
  can be shown much more easily. In particular, it lets us use initiality of
  the natural numbers to prove initiality of these integers. *)
Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable.
Require
 HoTTClasses.theory.naturals.
Require Import
 HoTTClasses.interfaces.abstract_algebra
 HoTTClasses.interfaces.naturals
 HoTTClasses.interfaces.integers
 HoTTClasses.theory.jections
 HoTTClasses.implementations.semiring_pairs
 HoTTClasses.tactics.ring_tac
 HoTTClasses.theory.rings.

Module NatPair.

Section contents.
Context `{Funext} `{Univalence} N `{Naturals@{N N} N}.
(* Add Ring N : (rings.stdlib_semiring_theory N). *)

Notation Npair := (SRPair.SRpair N).
Definition Z := Completion.R N.

(* Copy results from srpairs for performance / ease of calling. *)
Global Instance Z_plus : Plus Z := _.
Global Instance Z_mult : Mult Z := _.
Global Instance Z_zero : Zero Z := _.
Global Instance Z_one : One Z := _.
Global Instance Z_negate : Negate Z := _.

Global Instance Z_of_pair : Cast Npair Z := _.
Global Instance Z_of_nat : Cast N Z := compose Z_of_pair (SRPair.SRpair_inject _).

Definition Z_eq {x y : Npair} : SRPair.equiv x y -> ' x = ' y
  := Completion.path _.

Definition Z_equiv {x y : Npair} : ' x = ' y -> SRPair.equiv x y
  := Completion.related_path _.

Definition Z_rect : forall (P : Z -> Type) {sP : forall x, IsHSet (P x)}
  (dclass : forall x, P (' x))
  (dequiv : forall x y E,
    (Z_eq E) # (dclass x) = (dclass y)),
  forall q, P q
  := Completion.R_rect _.

Definition Z_compute P {sP} dclass dequiv x
  : @Z_rect P sP dclass dequiv (' x) = dclass x := 1.



Definition Z_ind : forall (P : Z -> Type) {sP : forall x, IsHProp (P x)}
  (dclass : forall x : Npair, P (' x)), forall x, P x
  := Completion.R_ind _.

Definition Z_ind2 : forall (P : Z -> Z -> Type) {sP : forall x y, IsHProp (P x y)}
  (dclass : forall x y : Npair, P (' x) (' y)), forall x y, P x y
  := Completion.R_ind2 _.

Definition Z_ind3 : forall (P : Z -> Z -> Z -> Type)
  {sP : forall x y z, IsHProp (P x y z)}
  (dclass : forall x y z : Npair, P (' x) (' y) (' z)),
  forall x y z, P x y z
  := Completion.R_ind3 _.

Definition Z_rec {T : Type} {sT : IsHSet T}
  : forall (dclass : Npair -> T)
  (dequiv : forall x y, SRPair.equiv x y -> dclass x = dclass y),
  Z -> T
  := Completion.R_rec _.

Definition Z_rec_compute T sT dclass dequiv x
  : @Z_rec T sT dclass dequiv (' x) = dclass x
  := 1.

Definition Z_rec2 {T} {sT : IsHSet T}
  : forall (dclass : Npair -> Npair -> T)
  (dequiv : forall x1 x2, SRPair.equiv x1 x2 -> forall y1 y2, SRPair.equiv y1 y2 ->
    dclass x1 y1 = dclass x2 y2),
  Z -> Z -> T
  := Completion.R_rec2 _.

Definition Z_rec2_compute {T sT} dclass dequiv x y
  : @Z_rec2 T sT dclass dequiv (' x) (' y) = dclass x y
  := 1.

Global Instance Z_set : IsHSet Z := _.
Global Instance Z_dec `{DecidablePaths N} : DecidablePaths Z := _.

Definition Z_plus_compute q r : ' q + ' r = ' (SRPair.pl _ q r) := idpath.

Definition Z_mult_compute q r : ' q * ' r = ' (SRPair.ml _ q r) := idpath.

Definition Z_negate_compute q : - ' q = ' (SRPair.opp _ q) := idpath.

Definition Z_zero_pair : @paths Z 0 (@cast N Z _ 0) := idpath.
Definition Z_one_pair : @paths Z 1 (@cast N Z _ 1) := idpath.

Local Instance Z_ring : Ring Z := _.

Global Instance N_to_Z_morphism : SemiRing_Morphism (cast N Z) := _.
Global Instance : Injective (cast N Z) := _.

Definition Npair_splits : forall n m, ' (SRPair.C n m) = ' n - ' m
  := Completion.SRpair_splits _.

(* NB: order stuff TODO *)
Typeclasses Opaque Z.

Lemma Z_to_ring_respects `{Ring B} :
  ∀ x y : SRPair.SRpair N,
  SRPair.equiv x y →
  naturals_to_semiring N B (SRPair.pos x) -
  naturals_to_semiring N B (SRPair.neg x)
  ≡ naturals_to_semiring N B (SRPair.pos y) -
    naturals_to_semiring N B (SRPair.neg y).
Proof.
unfold SRPair.equiv;intros [pa na] [pb nb];simpl;intros E.
apply (right_cancellation plus
  (naturals_to_semiring N B na + naturals_to_semiring N B nb)).
path_via (naturals_to_semiring N B pa + naturals_to_semiring N B nb);
[|path_via (naturals_to_semiring N B pb + naturals_to_semiring N B na)].
- path_via (naturals_to_semiring N B pa + naturals_to_semiring N B nb +
    (naturals_to_semiring N B na - naturals_to_semiring N B na)).
  + ring_with_nat.
  + rewrite plus_negate_r,plus_0_r. reflexivity.
- rewrite <-2!preserves_plus.
  apply ap;trivial.
- path_via (naturals_to_semiring N B pb + naturals_to_semiring N B na +
    (naturals_to_semiring N B nb - naturals_to_semiring N B nb)).
  + rewrite plus_negate_r,plus_0_r. reflexivity.
  + ring_with_nat.
Qed.

(* We show that Z is initial, and therefore a model of the integers. *)
Global Instance Z_to_ring: IntegersToRing Z.
Proof.
intros B ??????.
apply (Z_rec (fun s => naturals_to_semiring N _ (SRPair.pos s)
    + - naturals_to_semiring N _ (SRPair.neg s))).
exact Z_to_ring_respects.
Defined.

(* Hint Rewrite preserves_0 preserves_1 preserves_mult preserves_plus: preservation.
  doesn't work for some reason, so we use: *)
Ltac preservation F :=
   repeat (rewrite (rings.preserves_plus (f:=F)) ||
    rewrite (rings.preserves_mult (f:=F)) || rewrite (rings.preserves_0 (f:=F)) ||
    rewrite (rings.preserves_1 (f:=F)) || rewrite (preserves_negate (f:=F))).

Section for_another_ring.
  Context `{Ring R}.

(*   Add Ring R : (rings.stdlib_ring_theory R). *)

  Notation n_to_sr := (naturals_to_semiring N R).
  Notation z_to_r := (integers_to_ring Z R).

  Let preserves_plus : forall x y, z_to_r (x + y) = z_to_r x + z_to_r y.
  Proof.
  apply (Z_ind2 _).
  unfold z_to_r, Z_to_ring. simpl. intros.
  preservation (n_to_sr).
  rewrite negate_plus_distr. ring_with_nat.
  Qed.

  Let preserves_mult : forall x y, z_to_r (x * y) = z_to_r x * z_to_r y.
  Proof.
  apply (Z_ind2 _).
  unfold z_to_r, Z_to_ring. simpl. intros.
  preservation (n_to_sr).
  rewrite negate_plus_distr.
  rewrite plus_mult_distr_r,2!plus_mult_distr_l.
  rewrite negate_mult_negate,<-!negate_mult_distr_l,<-!negate_mult_distr_r.
  ring_with_nat.
  Qed.

  Let preserves_1: z_to_r 1 = 1.
  Proof.
  unfold z_to_r, Z_to_ring;simpl.
  preservation (n_to_sr).
  rewrite negate_0,plus_0_r;split.
  Qed.

  Let preserves_0: z_to_r 0 = 0.
  Proof.
  unfold z_to_r, Z_to_ring;simpl.
  preservation (n_to_sr).
  rewrite negate_0,plus_0_r;split.
  Qed.

  Global Instance z_to_ring_morphism : SemiRing_Morphism z_to_r.
  Proof.
  repeat (split; try apply _).
  - exact preserves_plus.
  - exact preserves_0.
  - exact preserves_mult.
  - exact preserves_1.
  Qed.

  Section for_another_morphism.
    Context (f : Z → R) `{!SemiRing_Morphism f}.

    Definition g : N → R := f ∘ cast N Z.

    Instance : SemiRing_Morphism g.
    Proof. unfold g. repeat (split; try apply _). Qed.

    Lemma same_morphism : forall x, z_to_r x = f x.
    Proof.
    apply (Z_ind _).
    intros x.
    unfold z_to_r,Z_to_ring;simpl.
    rewrite Npair_splits.
    preservation f.
    rewrite <-2!(naturals.to_semiring_unique g).
    reflexivity.
    Qed.
  End for_another_morphism.
End for_another_ring.

Global Instance Z_integers : Integers Z.
Proof.
split;try apply _.
exact @same_morphism.
Qed.

Context `{!NatDistance N}.

Lemma Z_abs_aux_0 : forall a b z : N, a + z = b -> z = 0 ->
  naturals_to_semiring N Z 0 ≡ ' {| SRPair.pos := a; SRPair.neg := b |}.
Proof.
intros a b z E E'.
rewrite (preserves_0 (A:=N)).
rewrite E',plus_0_r in E. rewrite E.
apply Z_eq. red;simpl. apply plus_comm.
Qed.

Lemma Z_abs_aux_neg : forall a b z : N, a + z = b ->
  naturals_to_semiring N Z z ≡ - ' {| SRPair.pos := a; SRPair.neg := b |}.
Proof.
intros a b z E.
rewrite <-(naturals.to_semiring_unique (cast N Z)).
apply Z_eq. red;simpl. rewrite plus_0_r,plus_comm;trivial.
Qed.

Lemma Z_abs_aux_pos : forall a b z : N, b + z = a ->
  naturals_to_semiring N Z z ≡ ' {| SRPair.pos := a; SRPair.neg := b |}.
Proof.
intros a b z E.
rewrite <-(naturals.to_semiring_unique (cast N Z)). apply Z_eq;red;simpl.
rewrite plus_0_r,plus_comm;trivial.
Qed.

(* We use decidability of equality on N
   to make sure we always go left when the inputs are equal.
   Otherwise we would have to truncate IntAbs. *)
Definition Z_abs_def : ∀ x : Npair,
  (∃ n : N, naturals_to_semiring N Z n ≡ ' x)
  ∨ (∃ n : N, naturals_to_semiring N Z n ≡ - ' x).
Proof.
intros [a b].
destruct (nat_distance_sig a b) as [[z E]|[z E]].
- destruct (decide (z = 0)) as [E'|_].
  + left. exists 0. apply Z_abs_aux_0 with z;trivial.
  + right. exists z. apply Z_abs_aux_neg;trivial.
- left. exists z. apply Z_abs_aux_pos;trivial.
Defined.

Lemma Z_abs_respects : ∀ (x y : Npair) (E : SRPair.equiv x y),
  transport
    (λ q : Z,
     (∃ n : N, naturals_to_semiring N Z n ≡ q)
     ∨ (∃ n : N, naturals_to_semiring N Z n ≡ - q)) (Z_eq E) (Z_abs_def x)
  ≡ Z_abs_def y.
Proof.
intros [pa pb] [na nb] E.
red in E; simpl in E.
unfold Z_abs_def.
destruct (nat_distance_sig pa pb) as [[z1 E1] | [z1 E1]];simpl.
- destruct (decide (z1 = 0)) as [E2 | E2].
  + rewrite Sum.transport_sum. rewrite Sigma.transport_sigma.
    destruct (nat_distance_sig na nb) as [[z2 E3] | [z2 E3]];
    [destruct (decide (z2 = 0)) as [E4 | E4]|];simpl.
    * apply ap.
      apply Sigma.path_sigma_hprop;simpl.
      apply PathGroupoids.transport_const.
    * destruct E4.
      rewrite <-E1,<-E3,E2,plus_0_r,<-(plus_0_r (na+pa)) in E.
      rewrite plus_assoc,(plus_comm pa) in E.
      apply (left_cancellation plus _) in E. trivial.
    * apply ap. apply Sigma.path_sigma_hprop. simpl.
      rewrite PathGroupoids.transport_const.
      rewrite E2,plus_0_r in E1.
      rewrite <-E3,E1 in E.
      apply (left_cancellation plus (pb + nb)).
      rewrite plus_0_r. etransitivity;[apply E|].
      ring_with_nat.
  + rewrite Sum.transport_sum,Sigma.transport_sigma.
    destruct (nat_distance_sig na nb) as [[z2 E3] | [z2 E3]];
    [destruct (decide (z2 = 0)) as [E4 | E4]|];simpl.
    * destruct E2.
      rewrite E4,plus_0_r in E3;rewrite <-E1,<-E3 in E.
      apply (left_cancellation plus (pa+na)).
      rewrite (plus_comm pa na),plus_0_r,<-plus_assoc.
      rewrite (plus_comm na pa). symmetry;trivial.
    * apply ap. apply Sigma.path_sigma_hprop.
      simpl. rewrite PathGroupoids.transport_const.
      rewrite <-E1,<-E3 in E.
      apply (left_cancellation plus (pa + na)).
      rewrite <-(plus_assoc pa na z2),(plus_comm pa na),<-plus_assoc.
      symmetry;trivial.
    * destruct E2.
      rewrite <-E1,<-E3 in E.
      assert (Erw : nb + z2 + (pa + z1) = (pa + nb) + (z2 + z1))
      by ring_with_nat.
      rewrite <-(plus_0_r (pa+nb)),Erw in E.
      apply (left_cancellation plus _),symmetry,naturals.zero_sum in E.
      apply E.
- rewrite Sum.transport_sum,Sigma.transport_sigma. simpl.
  destruct (nat_distance_sig na nb) as [[z2 E3] | [z2 E3]];
  [destruct (decide (z2 = 0)) as [E4 | E4]|];simpl.
  + apply ap. apply Sigma.path_sigma_hprop. simpl.
    rewrite PathGroupoids.transport_const.
    rewrite <-E1,<-E3,E4,plus_0_r in E.
    apply (left_cancellation plus (na+pb)).
    rewrite plus_0_r.
    path_via (pb + z1 + na). ring_with_nat.
  + destruct E4.
    rewrite <-E1,<-E3 in E.
    assert (Hrw : pb + z1 + (na + z2) = (na + pb) + (z1 + z2))
    by ring_with_nat.
    rewrite <-(plus_0_r (na+pb)),Hrw in E.
    apply (left_cancellation _ _),naturals.zero_sum in E.
    apply E.
  + apply ap,Sigma.path_sigma_hprop. simpl.
    rewrite PathGroupoids.transport_const.
    rewrite <-E1,<-E3 in E.
    apply (left_cancellation plus (pb+nb)).
    path_via (pb + z1 + nb);[|path_via (nb + z2 + pb)];ring_with_nat.
Qed.

Global Instance Z_abs : IntAbs Z N.
Proof.
red. apply (Z_rect _ Z_abs_def).
exact Z_abs_respects.
Qed.

Notation n_to_z := (naturals_to_semiring N Z).

Definition zero_product_aux a b :
  n_to_z a * n_to_z b = 0 → n_to_z a = 0 ∨ n_to_z b = 0.
Proof.
rewrite <-rings.preserves_mult.
rewrite <-!(naturals.to_semiring_unique (cast N Z)).
intros E.
rewrite Z_zero_pair in E. apply (injective _) in E.
apply zero_product in E.
destruct E as [E|E];rewrite E;[left|right];apply preserves_0.
Qed.

Global Instance Z_zero_product : ZeroProduct Z.
Proof.
intros x y E.
destruct (int_abs_sig Z N x) as [[a Ea]|[a Ea]],
  (int_abs_sig Z N y) as [[b Eb]|[b Eb]].
- rewrite <-Ea,<-Eb in E.
  apply zero_product_aux in E.
  rewrite <-Ea,<-Eb.
  trivial.
- apply (ap negate) in E. rewrite negate_mult_distr_r in E.
  rewrite <-Ea,<-Eb in E.
  rewrite negate_0 in E.
  apply zero_product_aux in E.
  destruct E as [E|E].
  + left;rewrite <-Ea;trivial.
  + right.
    apply (injective negate).
    rewrite negate_0,<-Eb;trivial.
- apply (ap negate) in E. rewrite negate_mult_distr_l in E.
  rewrite <-Ea,<-Eb in E.
  rewrite negate_0 in E.
  apply zero_product_aux in E.
  destruct E as [E|E].
  + left.
    apply (injective negate).
    rewrite negate_0,<-Ea;trivial.
  + right;rewrite <-Eb;trivial.
- rewrite <-negate_mult_negate,<-Ea,<-Eb in E.
  apply zero_product_aux in E.
  destruct E as [E|E].
  + left.
    apply (injective negate).
    rewrite negate_0,<-Ea;trivial.
  + right.
    apply (injective negate).
    rewrite negate_0,<-Eb;trivial.
Qed.

End contents.

End NatPair.
