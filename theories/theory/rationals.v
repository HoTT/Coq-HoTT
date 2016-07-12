Require Import
  HoTT.Types.Universe
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.rationals
  HoTTClasses.implementations.peano_naturals
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.implementations.field_of_fractions
  HoTTClasses.theory.dec_fields.

Module ExampleField.

Section Univ.
Context `{Funext} `{Univalence}.

Definition F := FracField.F (NatPair.Z nat).

Global Instance Fap : Apart F := fun x y => ~ x = y.

Instance F_trivialapart : TrivialApart F.
Proof.
split.
- apply _.
- reflexivity.
Qed.

Lemma F_field' : Field F.
Proof. exact _. Qed.

Global Instance F_field@{i} : Field F
  := F_field'@{i Ularge Set Set}.

Instance inject_nat : Cast nat F
  := compose (cast (NatPair.Z nat) F) (cast nat (NatPair.Z nat)).

Instance inject_nat_injective : Injective (cast nat F).
Proof.
apply jections.compose_injective;apply _.
Qed.

Instance inject_nat_preserving : SemiRingPreserving (cast nat F).
Proof.
apply compose_sr_morphism;apply _.
Qed.

Lemma repeat_is_inject : forall n : nat, repeat n (1 +) 0 = ' n :> F.
Proof.
induction n as [|n IHn].
- simpl. reflexivity.
- simpl. rewrite IHn. change (S n) with (1 + n).
  rewrite (preserves_plus (f:=cast nat F)).
  reflexivity.
Qed.

Lemma F_characteristic_0' : FieldCharacteristic F 0.
Proof.
change (forall n : nat, 0 < n ->
  (forall m, ~ n = 0 * m) <-> apart (repeat n (plus 1) 0) 0).
induction n as [|n IH].
- intros E. destruct (not_lt_0 _ E).
- intros E. destruct n as [|n].
  + simpl. rewrite plus_0_r.
    split;intros E'.
    * solve_propholds.
    * intros;rewrite mult_0_l.
      apply S_neq_0.
  + simpl. pose proof (IH (lt_0_S _)) as IH'.
    clear IH.
    split;intros E'.
    * intro H1.
      rewrite repeat_is_inject in H1.
      apply FracField.classes_eq_related in H1.
      red in H1;simpl in H1.
      rewrite !mult_1_r in H1. apply NatPair.related_path in H1.
      destruct (S_neq_0 _ H1).
    * intros. rewrite mult_0_l.
      apply S_neq_0.
Qed.

Global Instance F_characteristic_0@{i} : FieldCharacteristic F 0
  := F_characteristic_0'@{i Ularge Set Set Set
    i i i Set Ularge
    Ularge Set Set Set}.

End Univ.
End ExampleField.

Section contents.
Context `{Funext} `{Univalence}
  `{Rationals Q} `{!TrivialApart Q}.

Global Instance rational_1_neq_0 : PropHolds (@apart Q _ 1 0).
Proof.
red. apply trivial_apart.
intros E.
pose proof (ap (rationals_to_field Q ExampleField.F) E) as E'.
rewrite (preserves_1 (f:=rationals_to_field Q ExampleField.F)),
  (preserves_0 (f:=rationals_to_field Q ExampleField.F)) in E'.
revert E'. clear E.
pose proof ExampleField.F_characteristic_0 as E.
hnf in E. rewrite <-(plus_0_r 1).
refine (fst (E 1 _) _).
- apply lt_0_S.
- intros. simpl. apply S_neq_0.
Qed.

End contents.
