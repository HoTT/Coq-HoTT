Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric
  HoTTClasses.implementations.cauchy_completion
  HoTTClasses.implementations.partiality
  HoTTClasses.implementations.sierpinsky
  HoTTClasses.implementations.cauchy_reals.

Section compare_cauchy_rat.

Instance semidecidable_ishprop : forall (x : real) (q : Q),
  IsHProp (exists s : Sier, s <-> x < rat q).
Proof.
intros x q. apply Sigma.ishprop_sigma_disjoint.
intros a b [E1 E1'] [E2 E2'].
apply (antisymmetry (<=));apply imply_le;intros E3;auto.
Qed.

Definition semidecidable_compare_rat_sig
  : forall x q, exists s : Sier, s <-> x < rat q.
Proof.
apply (C_ind0 _ (fun x => forall q, _)).
- intros q r. exists (semi_decide (q < r)).
  split;intros E.
  + apply rat_lt_preserving,semi_decidable,E.
  + apply rat_lt_reflecting,semi_decidable in E;apply E.
- intros x IH q.
  exists (semi_decide@{UQ} (merely (exists e : Q+,
    merely (exists d : Q+, (IH e (q - ' e - ' d)).1)))).
  split;intros E.
  + apply semi_decidable in E.
    revert E;apply (Trunc_ind _);intros [e E];
    revert E;apply (Trunc_ind _);intros [d E].
    set (s := _ : exists _, _) in E;apply s.2 in E;clear s.
    apply (fun E => Rlt_close_rat_plus _ _ E _ _ (equiv_lim _ _ d _)) in E.
    assert (Hrw : q - ' e - ' d + ' (d + e) = q)
    by abstract ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw in E;clear Hrw.
    trivial.
  + apply (snd semi_decidable).
    apply R_archimedean in E;revert E;apply (Trunc_ind _);intros [r [E1 E2]].
    apply rat_lt_reflecting in E2. pose (e := Qpos_diff _ _ E2).
    apply tr;exists (e/4);apply tr;exists (e/4).
    set (s := _ : sigT _);apply s.2;clear s.
    pose proof (fun a b => Rlt_close_rat_plus _ _ E1 _ _
      (symmetry _ _ (equiv_lim _ _ a b))) as E3.
    assert (Hrw : q - ' (e / 4) - ' (e / 4) = r + ' (e / 4 + e / 4));
    [|rewrite Hrw;apply E3].
    assert (Hrw : 4 / 4 = 1 :> Q).
    { apply dec_recip_inverse. apply lt_ne_flip. solve_propholds. }
    rewrite <-(mult_1_r q),<-(mult_1_r r),<-Hrw.
    unfold e;clear e. repeat (unfold cast;simpl).
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
Defined.

Instance semidecide_compare_rat x q : SemiDecide (x < rat q)
  := (semidecidable_compare_rat_sig x q).1.
Instance semidecidable_compare_rat x q : SemiDecidable (x < rat q)
  := (semidecidable_compare_rat_sig x q).2.

Instance semidecide_compare_rat_alt x q : SemiDecide (rat q < x)
  := semi_decide (- x < rat (- q)).
Instance semidecidable_compare_rat_alt
  : forall x q, SemiDecidable (rat q < x).
Proof.
intros x q;split;intros E.
- apply flip_lt_negate,semidecidable_compare_rat,E.
- apply semidecidable_compare_rat.
  change (- x < - rat q). apply (snd (flip_lt_negate _ _)),E.
Qed.

Lemma compare_rat_disjoint : forall x q,
  disjoint (semi_decide (rat q < x)) (semi_decide (x < rat q)).
Proof.
intros x q E1 E2;
apply semidecidable_compare_rat_alt in E1;apply semidecidable_compare_rat in E2.
generalize (conj E1 E2). apply (lt_antisym).
Qed.

Definition compare_cauchy_rat : real -> Q -> partial bool
  := fun x q => interleave _ _ (compare_rat_disjoint x q).

Lemma compare_cauchy_rat_pr : forall a q b, compare_cauchy_rat a q = eta _ b <->
  match b with
  | true => rat q < a
  | false => a < rat q
  end.
Proof.
intros a q b.
split.
- intros E;apply interleave_pr in E.
  destruct b;apply semi_decidable;exact E.
- intros E. destruct b.
  + apply interleave_top_l,(snd semi_decidable),E.
  + apply interleave_top_r,(snd semi_decidable),E.
Qed.

Lemma compare_cauchy_rat_self : forall q, compare_cauchy_rat (rat q) q = bot _.
Proof.
intros. apply interleave_bot;apply imply_le;intros E;
apply semi_decidable,(irreflexivity _) in E;destruct E.
Qed.

End compare_cauchy_rat.
