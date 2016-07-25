Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.orders.lattices
  HoTTClasses.implementations.natpair_integers.


Local Set Universe Minimization ToSet.

Coercion trunctype_type : TruncType >-> Sortclass.
Coercion equiv_fun : Equiv >-> Funclass.

Section contents.
Context `{Funext} `{Univalence}.
Universe UQ.
Context {Q : Type@{UQ} } {Qap : Apart@{UQ UQ} Q}
  {Qplus : Plus Q} {Qmult : Mult Q}
  {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
  {Qle : Le@{UQ UQ} Q} {Qlt : Lt@{UQ UQ} Q}
  {QtoField : RationalsToField@{UQ UQ UQ UQ} Q}
  {Qrats : Rationals@{UQ UQ UQ UQ UQ UQ UQ UQ UQ UQ} Q}
  {Qtrivialapart : TrivialApart Q} {Qdec : DecidablePaths Q}
  {Qmeet : Meet Q} {Qjoin : Join Q} {Qlattice : LatticeOrder Qle}
  {Qle_total : TotalRelation (@le Q _)}
  {Qabs : Abs Q}.

Global Instance rational_1_neq_0 : PropHolds (@apart Q _ 1 0).
Proof.
red. apply trivial_apart. solve_propholds.
Qed.

Record Qpos@{} : Type@{UQ} := mkQpos { pos : Q; is_pos : 0 < pos }.
Notation "Q+" := Qpos.

Global Instance Qpos_Q@{} : Cast Qpos Q := pos.
Arguments Qpos_Q /.

Lemma Qpos_plus_pr@{} : forall a b : Qpos, 0 < 'a + 'b.
Proof.
intros.
apply semirings.pos_plus_compat;apply is_pos.
Qed.

Global Instance Qpos_plus@{} : Plus Qpos := fun a b => mkQpos _ (Qpos_plus_pr a b).

Global Instance pos_is_pos@{} : forall q : Q+, PropHolds (0 < ' q)
  := is_pos.

Lemma pos_eq@{} : forall a b : Q+, @paths Q (' a) (' b) -> a = b.
Proof.
intros [a Ea] [b Eb] E.
change (a = b) in E.
destruct E;apply ap;apply path_ishprop.
Qed.

Global Instance Qpos_one@{} : One Q+.
Proof.
exists 1. apply lt_0_1.
Defined.

Global Instance Qpos_mult@{} : Mult Q+.
Proof.
intros a b;exists (' a * ' b).
solve_propholds.
Defined.

Global Instance qpos_plus_comm@{} : Commutative (@plus Q+ _).
Proof.
hnf. intros.
apply pos_eq. change (' x + ' y = ' y + ' x).
apply plus_comm.
Qed.

Global Instance qpos_mult_comm@{} : Commutative (@mult Q+ _).
Proof.
hnf;intros;apply pos_eq,mult_comm.
Qed.

Global Instance pos_recip@{} : DecRecip Q+.
Proof.
intros e. exists (/ ' e).
apply pos_dec_recip_compat.
solve_propholds.
Defined.

Global Instance pos_of_nat@{} : Cast nat Q+.
Proof.
intros n. destruct n as [|k].
- exists 1;apply lt_0_1.
- exists (naturals_to_semiring nat Q (S k)).
  induction k as [|k Ik].
  + change (0 < 1). apply lt_0_1.
  + change (0 < 1 + naturals_to_semiring nat Q (S k)).
    set (K := naturals_to_semiring nat Q (S k)) in *;clearbody K.
    apply pos_plus_compat.
    apply lt_0_1.
    trivial.
Defined.

Lemma pos_recip_r@{} : forall e : Q+, e / e = 1.
Proof.
intros;apply pos_eq.
unfold dec_recip,cast,pos_recip;simpl.
change (' e / ' e = 1). apply dec_recip_inverse.
apply lt_ne_flip. solve_propholds.
Qed.

Lemma pos_recip_r'@{} : forall e : Q+, @paths Q (' e / ' e) 1.
Proof.
intros. change (' (e / e) = 1). rewrite pos_recip_r. reflexivity.
Qed.

Lemma pos_mult_1_r@{} : forall e : Q+, e * 1 = e.
Proof.
intros;apply pos_eq. apply mult_1_r.
Qed.

Lemma pos_split2@{} : forall e : Q+, e = e / 2 + e / 2.
Proof.
intros.
path_via (e * (2 / 2)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (2 / 2) = ' e / 2 + ' e / 2).
  ring_tac.ring_with_nat.
Qed.

Lemma pos_split3@{} : forall e : Q+, e = e / 3 + e / 3 + e / 3.
Proof.
intros.
path_via (e * (3 / 3)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (3 / 3) = ' e / 3 + ' e / 3 + ' e / 3).
  ring_tac.ring_with_nat.
Qed.

Global Instance Qpos_mult_assoc@{} : Associative (@mult Q+ _).
Proof.
hnf.
intros;apply pos_eq.
apply mult_assoc.
Qed.

Global Instance Qpos_plus_assoc@{} : Associative (@plus Q+ _).
Proof.
hnf.
intros;apply pos_eq.
apply plus_assoc.
Qed.

Global Instance Qpos_mult_1_l@{} : LeftIdentity (@mult Q+ _) 1.
Proof.
hnf;intros;apply pos_eq;apply mult_1_l.
Qed.

Lemma pos_recip_through_plus@{} : forall a b c : Q+,
  a + b = c * (a / c + b / c).
Proof.
intros. path_via ((a + b) * (c / c)).
- rewrite pos_recip_r;apply pos_eq,symmetry,mult_1_r.
- apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma pos_unconjugate@{} : forall a b : Q+, a * b / a = b.
Proof.
intros. path_via (a / a * b).
- apply pos_eq;ring_tac.ring_with_nat.
- rewrite pos_recip_r;apply Qpos_mult_1_l.
Qed.

Global Instance Qpos_meet@{} : Meet Q+.
Proof.
intros a b. exists (meet (' a) (' b)).
apply not_le_lt_flip. intros E.
destruct (total_meet_either (' a) (' b)) as [E1|E1];
rewrite E1 in E;(eapply le_iff_not_lt_flip;[exact E|]);
solve_propholds.
Defined.

Global Instance Qpos_join@{} : Join Q+.
Proof.
intros a b. exists (join (' a) (' b)).
apply not_le_lt_flip. intros E.
destruct (total_join_either (' a) (' b)) as [E1|E1];
rewrite E1 in E;(eapply le_iff_not_lt_flip;[exact E|]);
solve_propholds.
Defined.

Lemma Q_sum_eq_join_meet@{} : forall a b c d : Q, a + b = c + d ->
  a + b = join a c + meet b d.
Proof.
intros ???? E.
destruct (total le a c) as [E1|E1].
- rewrite (join_r _ _ E1). rewrite meet_r;trivial.
  apply (order_preserving (+ b)) in E1.
  rewrite E in E1. apply (order_reflecting (c +)). trivial.
- rewrite (join_l _ _ E1).
  rewrite meet_l;trivial.
  apply (order_reflecting (a +)). rewrite E. apply (order_preserving (+ d)).
  trivial.
Qed.

Lemma Qpos_sum_eq_join_meet@{} : forall a b c d : Q+, a + b = c + d ->
  a + b = join a c + meet b d.
Proof.
intros ???? E.
apply pos_eq;apply Q_sum_eq_join_meet.
change (' a + ' b) with (' (a + b)). rewrite E;reflexivity.
Qed.

Lemma Qpos_le_lt_min : forall a b : Q+, ' a <= ' b ->
  exists c ca cb, a = c + ca /\ b = c + cb.
Proof.
intros a b E. exists (a/2),(a/2).
simple refine (existT _ _ _);simpl.
- exists (' (a / 2) + (' b - ' a)).
  apply nonneg_plus_lt_compat_r.
  + apply (snd (flip_nonneg_minus _ _)). trivial.
  + solve_propholds.
- split.
  + apply pos_split2.
  + apply pos_eq. unfold cast at 2;simpl.
    unfold cast at 3;simpl.
    set (a':=a/2);rewrite (pos_split2 a);unfold a';clear a'.
    ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

Lemma Qpos_lt_min@{} : forall a b : Q+, exists c ca cb, a = c + ca /\ b = c + cb.
Proof.
intros.
destruct (total le (' a) (' b)) as [E|E].
- apply Qpos_le_lt_min;trivial.
- apply Qpos_le_lt_min in E. destruct E as [c [cb [ca [E1 E2]]]].
  exists c,ca,cb;auto.
Qed.

Definition Qpos_diff : forall q r : Q, q < r -> Q+.
Proof.
intros q r E;exists (r-q).
apply (snd (flip_pos_minus _ _) E).
Defined.

Lemma Qpos_diff_pr@{} : forall q r E, r = q + ' (Qpos_diff q r E).
Proof.
intros q r E. change (r = q + (r - q)).
abstract ring_tac.ring_with_integers (NatPair.Z nat).
Qed.

End contents.

Arguments Qpos Q {_ _}.
