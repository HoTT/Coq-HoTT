Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.field_of_fractions
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.theory.lattices
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric
  HoTTClasses.implementations.partiality
  HoTTClasses.implementations.sierpinsky.

Local Set Universe Minimization ToSet.

Definition QPred : Type@{UQ} := Q -> Sier.

Section iscut_def.
Variables (lower upper : QPred).

Class IsCut@{} : Type@{UQ} :=
  { iscut_lower_inhab : merely@{UQ} (exists q, lower q)
  ; iscut_upper_inhab : merely@{UQ} (exists q, upper q)
  ; iscut_lower_rounded : forall q, iff@{Set UQ UQ} (lower q)
    (merely (exists r, q < r /\ lower r))
  ; iscut_upper_rounded : forall r, iff@{Set UQ UQ} (upper r)
    (merely (exists q, q < r /\ upper q))
  ; iscut_cut_disjoint : forall q, lower q -> upper q -> Empty
  ; iscut_cut_located : forall q r, q < r -> hor (lower q) (upper r) }.
End iscut_def.

Record Cut@{} :=
  { lower : QPred
  ; upper : QPred
  ; cut_iscut : IsCut lower upper }.
Global Existing Instance cut_iscut.

Definition lower_inhab (c : Cut) := iscut_lower_inhab (lower c) _.
Definition upper_inhab (c : Cut) := iscut_upper_inhab (lower c) _.
Definition lower_rounded (c : Cut) := iscut_lower_rounded (lower c) _.
Definition upper_rounded (c : Cut) := iscut_upper_rounded (lower c) _.
Definition cut_disjoint (c : Cut) := iscut_cut_disjoint (lower c) _.
Definition cut_located (c : Cut) := iscut_cut_located (lower c) _.

Lemma lower_le : forall a q r, lower a q -> r <= q -> lower a r.
Proof.
intros a q r E1 E2.
destruct (le_or_lt q r) as [E3|E3].
- destruct (antisymmetry le _ _ E2 E3);trivial.
- apply lower_rounded. apply tr. exists q;auto.
Qed.

Lemma upper_le : forall a q r, upper a q -> q <= r -> upper a r.
Proof.
intros a q r E1 E2.
destruct (le_or_lt r q) as [E3|E3].
- destruct (antisymmetry le _ _ E2 E3);trivial.
- apply upper_rounded. apply tr. exists q;auto.
Qed.

Definition IsCut_conjunction l u : IsCut l u -> _
  := fun c => (iscut_lower_inhab l u, iscut_upper_inhab l u,
    iscut_lower_rounded l u, iscut_upper_rounded l u,
    iscut_cut_disjoint l u, iscut_cut_located l u).

Global Instance iscut_conj_isequiv {l u}
  : IsEquiv@{UQ UQ} (IsCut_conjunction@{UQ UQ} l u).
Proof.
simple refine (BuildIsEquiv _ _ _ _ _ _ _).
- intros E;split;apply E.
- red;simpl. intros [[[[[? ?] ?] ?] ?] ?]. reflexivity.
- red;simpl. reflexivity.
- simpl. reflexivity.
Defined.

Section contents.
Context `{Funext} `{Univalence}.

Global Instance IsCut_hprop : forall l u, IsHProp (IsCut l u).
Proof.
intros. apply (@trunc_equiv _ _ ((IsCut_conjunction l u)^-1) _ _ _).
Qed.

Lemma cut_eq : forall a b : Cut, lower a = lower b -> upper a = upper b ->
  a = b.
Proof.
intros [la ua Ea] [lb ub Eb];simpl;intros E1 E2;destruct E1,E2;apply ap.
apply path_ishprop.
Qed.

Instance cut_isset : IsHSet Cut.
Proof.
apply (@HSet.isset_hrel_subpaths _
  (fun a b => lower a = lower b /\ upper a = upper b)).
- intros a;split;reflexivity.
- apply _.
- intros a b E;apply cut_eq;apply E.
Qed.

Lemma cut_orders : forall (c : Cut) (q r : Q), lower c q -> upper c r -> q < r.
Proof.
intros c q r E1 E2.
destruct (le_or_lt r q) as [E|E];trivial.
destruct (cut_disjoint c q);trivial.
apply upper_le with r;trivial.
Qed.

Lemma cut_bounds : forall (c : Cut) (e : Q+),
  merely (exists q r, r - q < ' e /\ lower c q /\ upper c r).
Proof.
intros c e.
generalize (lower_inhab c);apply (Trunc_ind _);intros [q Eq].
generalize (upper_inhab c);apply (Trunc_ind _);intros [r Er].
Abort.

Instance pred_plus : Plus QPred.
Proof.
intros x y q.
apply (EnumerableSup Q). intros r. apply (EnumerableSup Q). intros s.
exact (meet (meet (x r) (y s)) (DecSier (q = r + s))).
Defined.
Arguments pred_plus _ _ / _.

Lemma pred_plus_pr : forall a b : QPred,
  forall q, (a + b) q <-> merely (exists r s, a r /\ b s /\ q = r + s).
Proof.
unfold plus at 1;simpl. intros a b q;split.
- intros E.
  apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);intros [r E].
  apply top_le_enumerable_sup in E;revert E;apply (Trunc_ind _);intros [s E].
  apply top_le_meet in E;destruct E as [E1 E3].
  apply top_le_meet in E1;destruct E1 as [E1 E2].
  apply dec_sier_pr in E3.
  apply tr;exists r,s;auto.
- apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
  apply top_le_enumerable_sup. apply tr;exists r.
  apply top_le_enumerable_sup. apply tr;exists s.
  repeat (apply top_le_meet;split);trivial.
  apply dec_sier_pr;trivial.
Qed.

Instance plus_iscut : forall a b : Cut,
  IsCut (lower a + lower b) (upper a + upper b).
Proof.
intros a b;split.
- generalize (lower_inhab a).
  apply (Trunc_ind _);intros [r Er].
  generalize (lower_inhab b).
  apply (Trunc_ind _);intros [s Es].
  apply tr;exists (r+s). apply pred_plus_pr.
  apply tr;exists r,s;auto.
- generalize (upper_inhab a).
  apply (Trunc_ind _);intros [r Er].
  generalize (upper_inhab b).
  apply (Trunc_ind _);intros [s Es].
  apply tr;exists (r+s). apply pred_plus_pr.
  apply tr;exists r,s;auto.
- intros q;split.
  + intros E. apply pred_plus_pr in E.
    revert E;apply (Trunc_ind _);intros [r [s [E1 [E2 E3]]]].
    apply (lower_rounded a) in E1.
    apply (lower_rounded b) in E2.
    revert E1;apply (Trunc_ind _);intros [r' [E1 E1']];
    revert E2;apply (Trunc_ind _);intros [s' [E2 E2']].
    apply tr;exists (r' + s'). split.
    * rewrite E3. apply plus_lt_compat;trivial.
    * apply pred_plus_pr. apply tr;eauto.
  + apply (Trunc_ind _);intros [q' [E1 E2]].
    apply pred_plus_pr in E2. revert E2.
    apply (Trunc_ind _);intros [r' [s' [E2 [E3 E4]]]].
    assert (Hq : q = (r' - (q' - q)) + s')
    by (rewrite E4;ring_tac.ring_with_integers (NatPair.Z nat)).
    rewrite Hq. apply pred_plus_pr.
    apply tr;econstructor;econstructor;split;[|split;[|reflexivity]];trivial.
    apply lower_le with r';trivial.
    apply flip_le_minus_l. apply nonneg_plus_le_compat_r.
    apply (snd (flip_nonneg_minus _ _)). apply lt_le;trivial.
- intros r;split.
  + intros E. apply pred_plus_pr in E.
    revert E;apply (Trunc_ind _);intros [q [s [E1 [E2 E3]]]].
    apply (upper_rounded a) in E1.
    apply (upper_rounded b) in E2.
    revert E1;apply (Trunc_ind _);intros [r' [E1 E1']];
    revert E2;apply (Trunc_ind _);intros [s' [E2 E2']].
    apply tr;exists (r' + s'). split.
    * rewrite E3. apply plus_lt_compat;trivial.
    * apply pred_plus_pr. apply tr;eauto.
  + apply (Trunc_ind _);intros [r' [E1 E2]].
    apply pred_plus_pr in E2. revert E2.
    apply (Trunc_ind _);intros [q' [s' [E2 [E3 E4]]]].
    assert (Hr : r = (q' - (r' - r)) + s')
    by (rewrite E4;ring_tac.ring_with_integers (NatPair.Z nat)).
    rewrite Hr. apply pred_plus_pr.
    apply tr;econstructor;econstructor;split;[|split;[|reflexivity]];trivial.
    apply upper_le with q';trivial.
    apply nonneg_plus_le_compat_r. rewrite <-negate_swap_r.
    apply (snd (flip_nonneg_minus _ _)). apply lt_le;trivial.
- intros q E1 E2.
  apply pred_plus_pr in E1;apply pred_plus_pr in E2.
  revert E1;apply (Trunc_ind _);intros [r1 [s1 [E1 [E1' E1'']]]].
  revert E2;apply (Trunc_ind _);intros [r2 [s2 [E2 [E2' E2'']]]].
  rewrite E1'' in E2'';clear E1'' q.
  destruct (total le r1 r2) as [E3|E3].
  + destruct (total le s1 s2) as [E4|E4].
    * assert (E5 : r2 <= r1).
      { apply not_lt_le_flip. intros E5.
        assert (E6 : r1 + s1 < r2 + s2)
        by (apply plus_lt_le_compat;trivial).
        rewrite E2'' in E6. revert E6;apply (irreflexivity lt). }
      apply (cut_disjoint a r2);trivial. apply lower_le with r1;trivial.
    * apply (cut_disjoint b s1);trivial. apply upper_le with s2;trivial.
  + apply (cut_disjoint a r2);trivial. apply lower_le with r1;trivial.
- intros q r E.
Abort. (* further lemmas required *)

Global Instance CutPlus : Plus Cut.
Proof.
intros x y.
apply (Build_Cut (lower x + lower y) (upper x + upper y)).
Fail apply plus_iscut.
Abort.

End contents.

