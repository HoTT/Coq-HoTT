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

Section contents.
Context `{Funext} `{Univalence} `{Naturals N}.
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

Global Instance : SemiRing_Morphism (cast N Z) := _.
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

  Ltac derive_preservation f := unfold integers_to_ring; simpl;
    preservation f; ring_with_nat.

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

  Global Instance: SemiRing_Morphism z_to_r.
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

    Instance: SemiRing_Morphism g.
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

Global Instance Z_abs : IntAbs Z N.
Proof.
red. (* Not hprop, what do? *)
Abort.

Notation n_to_z := (naturals_to_semiring N Z).

(* Without this opaque, typeclasses find a proof of Injective zero,
 from [id_injective] *)
Typeclasses Opaque zero.

Let zero_product_aux a b :
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
red.
(* Not hprop, what do? *)
Abort.
End contents.
