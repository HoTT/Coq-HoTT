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
  HoTTClasses.implementations.cauchy_reals
  HoTTClasses.implementations.dedekind.

Section cut_of_cauchy.

Definition cut_of_cauchy : Cast real Cut
  := lipschitz_extend Q (cast Q Cut) 1.

Definition cut_of_cauchy_rat : forall q : Q, cut_of_cauchy (rat q) = ' q
  := fun _ => idpath.

Global Instance cut_of_cauchy_nonexpanding : NonExpanding cut_of_cauchy
  := lipschitz_nonexpanding _.

Lemma cut_of_cauchy_upper_pr : forall a q, upper (cut_of_cauchy a) q <-> a < rat q.
Proof.
apply (C_ind0 Q (fun a => forall q, upper (cut_of_cauchy a) q <-> a < rat q)).
- intros q r;split.
  + intros E.
    apply rat_lt_preserving,semi_decidable. trivial.
  + intros E;apply rat_lt_reflecting,semi_decidable in E;
    trivial.
- intros x IHx q;split.
  + intros E. unfold cut_of_cauchy in E.
    rewrite lipschitz_extend_lim in E.
    simpl in E. apply lim_upper_cut_pr in E.
    simpl in E. revert E;apply (Trunc_ind _);intros [e [d E]].
    rewrite Qpos_recip_1,Qpos_mult_1_r in E.
    apply IHx in E.
    apply (fun E => Rlt_close_rat_plus _ _ E _ _ (equiv_lim _ _ d _)) in E.
    assert (Hrw : q - ' e - ' d + ' (d + e) = q)
    by abstract ring_tac.ring_with_integers (NatPair.Z nat);
    rewrite Hrw in E;clear Hrw.
    trivial.
  + intros E. unfold cut_of_cauchy;rewrite lipschitz_extend_lim.
    simpl. apply lim_upper_cut_pr;simpl.
    change (merely (exists e d, upper (cut_of_cauchy (x (e / 1)))
      (q - ' e - ' d))).
    apply R_archimedean in E;revert E;apply (Trunc_ind _);intros [r [E1 E2]].
    apply rat_lt_reflecting in E2.
    pose proof (fun a b => Rlt_close_rat_plus _ _ E1 _ _
      (symmetry _ _ (equiv_lim _ _ a b))) as E3.
    pose proof (fun a b => snd (IHx _ _) (E3 a b)) as E4. clear E3.
    pose (e := Qpos_diff _ _ E2).
    apply tr;exists (e/4),(e/4).
    rewrite Qpos_recip_1,Qpos_mult_1_r.
    assert (Hrw : q - ' (e / 4) - ' (e / 4) = r + ' (e / 4 + e / 4));
    [|rewrite Hrw;apply E4].
    assert (Hrw : 4 / 4 = 1 :> Q).
    { apply dec_recip_inverse. apply lt_ne_flip. solve_propholds. }
    rewrite <-(mult_1_r q),<-(mult_1_r r),<-Hrw.
    unfold e;clear e. repeat (unfold cast;simpl).
    abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma cut_of_cauchy_preserves_plus : forall a b,
  cut_of_cauchy (a + b) = cut_of_cauchy a + cut_of_cauchy b.
Proof.
intros a. apply (unique_continuous_extension _).
{ apply _. }
{ change (Continuous ((cut_of_cauchy a +) ∘ cut_of_cauchy)).
  apply continuous_compose.
  { apply nonexpanding_continuous. apply CutPlus_nonexpanding_l. }
  apply _. }
intros r;revert a. apply (unique_continuous_extension _).
{ apply _. }
{ change (Continuous ((+ cut_of_cauchy (rat r)) ∘ cut_of_cauchy)).
  apply _. }
intros q.
change (' (q + r) = ' q + ' r :> Cut).
apply CutPlus_rat.
Qed.

Lemma cut_of_cauchy_preserves_neg : forall a,
  cut_of_cauchy (- a) = - cut_of_cauchy a.
Proof.
apply (@groups.preserves_negate real plus 0 negate _ Cut plus 0 negate _).
split.
- hnf. exact cut_of_cauchy_preserves_plus.
- hnf. reflexivity.
Qed.

Lemma cut_of_cauchy_lower_pr : forall a q, lower (cut_of_cauchy a) q <-> rat q < a.
Proof.
intros.
rewrite <-(negate_involutive a),cut_of_cauchy_preserves_neg.
change (IsTop (lower (- cut_of_cauchy (- a)) q)) with
  (IsTop (upper (cut_of_cauchy (- a)) (- q))).
rewrite involutive.
split;intros E.
- apply cut_of_cauchy_upper_pr in E.
  change (- a < - (rat q)) in E.
  apply flip_lt_negate. trivial.
- apply cut_of_cauchy_upper_pr. change (- a < - (rat q)).
    apply flip_lt_negate in E. trivial.
Qed.

Lemma cut_of_cauchy_lt_preserving : StrictlyOrderPreserving cut_of_cauchy.
Proof.
intros a b E.
generalize (R_archimedean _ _ E);apply (Trunc_ind _);intros [q [E1 E2]].
apply tr. exists q. split.
- apply cut_of_cauchy_upper_pr. trivial.
- apply cut_of_cauchy_lower_pr. trivial.
Qed.

Lemma cut_of_cauchy_lt_reflecting : StrictlyOrderReflecting cut_of_cauchy.
Proof.
intros a b;apply (Trunc_ind _). intros [q [E1 E2]].
apply cut_of_cauchy_upper_pr in E1;apply cut_of_cauchy_lower_pr in E2.
transitivity (rat q);trivial.
Qed.

Global Instance cut_of_cauchy_lt_embedding : StrictOrderEmbedding cut_of_cauchy.
Proof.
split.
- apply cut_of_cauchy_lt_preserving.
- apply cut_of_cauchy_lt_reflecting.
Qed.

Lemma cut_of_cauchy_le_preserving : OrderPreserving cut_of_cauchy.
Proof.
apply full_pseudo_order_preserving.
Qed.

Lemma cut_of_cauchy_le_reflecting : OrderReflecting cut_of_cauchy.
Proof.
apply full_pseudo_order_reflecting.
Qed.

Global Instance cut_of_cauchy_le_embedding : OrderEmbedding cut_of_cauchy.
Proof.
split.
- apply cut_of_cauchy_le_preserving.
- apply cut_of_cauchy_le_reflecting.
Qed.

Global Instance cut_of_cauchy_strong_inj : StrongInjective cut_of_cauchy.
Proof.
apply pseudo_order_embedding_inj.
Qed.

Global Instance cauchy_lt_rat_semi_decide : forall x q, SemiDecide (rat q < x)
  := fun x q => lower (cut_of_cauchy x) q.
Arguments cauchy_lt_rat_semi_decide _ _ /.

Global Instance cauchy_lt_rat_semi_decidable
  : forall x q, SemiDecidable (rat q < x).
Proof.
apply cut_of_cauchy_lower_pr.
Qed.

Definition compare_cauchy_rat : real -> Q -> partial bool
  := fun x q => compare_cut_rat (cut_of_cauchy x) q.

Lemma compare_cauchy_rat_pr : forall a q b, compare_cauchy_rat a q = eta _ b <->
  match b with
  | true => rat q < a
  | false => a < rat q
  end.
Proof.
intros a q b.
split.
- intros E;apply compare_cut_rat_pr in E.
  destruct b;apply (strictly_order_reflecting cut_of_cauchy);exact E.
- intros E;apply compare_cut_rat_pr.
  change (' q) with (cut_of_cauchy (rat q)).
  destruct b;apply (strictly_order_preserving cut_of_cauchy);exact E.
Qed.

Lemma compare_cauchy_rat_self : forall q, compare_cauchy_rat (rat q) q = bot _.
Proof.
intros. apply compare_cut_rat_self.
Qed.

End cut_of_cauchy.

