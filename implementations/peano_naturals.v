Require Coq.Init.Peano.
Require Import HoTT.Basics.Decidable HoTT.Types.Sum.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.orders
  HoTTClasses.theory.rings
  HoTTClasses.orders.semirings
  HoTTClasses.theory.apartness.

Instance nat_0: Zero nat := 0%nat.
Instance nat_1: One nat := 1%nat.

Fixpoint add n m :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end.

Instance nat_plus: Plus nat := add.

Fixpoint mul n m :=
  match n with
  | 0 => 0
  | S p => m + (mul p m)
  end.

Instance nat_mult: Mult nat := mul.

Ltac simpl_nat :=
  change plus with nat_plus;
  change mult with nat_mult;
  simpl;
  change nat_plus with plus; change nat_mult with mult.

Local Instance add_assoc : Associative (plus : Plus nat).
Proof.
intros a;induction a as [|a IH];intros b c.
+ reflexivity.
+ change ((a + (b + c)).+1 = (a + b + c).+1).
  apply ap,IH.
Qed.

Lemma add_0_r : forall x, x + 0 = x.
Proof.
intros a;induction a as [|a IH].
+ reflexivity.
+ apply (ap S),IH.
Qed.

Lemma add_S_r : forall a b, a + S b = S (a + b).
Proof.
induction a as [|a IHa];intros b.
- reflexivity.
- simpl_nat. apply (ap S),IHa.
Qed.

Lemma add_S_l a b : S a + b = S (a + b).
Proof 1.

Lemma add_0_l a : 0 + a = a.
Proof 1.

Local Instance add_comm : Commutative (plus : Plus nat).
Proof.
intros a;induction a as [|a IHa];intros b;induction b as [|b IHb].
- reflexivity.
- change (S b = S (b + 0)). apply ap,IHb.
- apply (ap S),IHa.
- change (S (a + S b) = S (b + S a)).
  rewrite IHa,<-IHb. apply (ap S),(ap S),symmetry,IHa.
Qed.

Local Instance add_mul_distr_l : LeftDistribute (mult :Mult nat) (plus:Plus nat).
Proof.
hnf. induction a as [|a IHa];simpl_nat.
- intros _ _;reflexivity.
- intros. rewrite IHa.
  rewrite <-(associativity b), (associativity c), (commutativity c),
  <-(associativity (a*b)), (associativity b).
  reflexivity.
Qed.

Lemma mul_0_r : forall a:nat, a * 0 = 0.
Proof.
induction a;simpl_nat;trivial.
Qed.

Lemma mul_S_r : forall a b, a * S b = a + a * b.
Proof.
induction a as [|a IHa];intros b;simpl_nat.
- trivial.
- simpl_nat. rewrite IHa.
  rewrite (associativity b a), (commutativity (f:=plus) b a), <-(associativity a b).
  reflexivity.
Qed.

Local Instance mul_comm : Commutative (mult : Mult nat).
Proof.
hnf. intros a;induction a as [|a IHa];simpl_nat.
- intros;apply symmetry,mul_0_r.
- intros b;rewrite IHa. rewrite mul_S_r,<-IHa. reflexivity.
Qed.

Local Instance mul_assoc : Associative (mult : Mult nat).
Proof.
hnf. intros a;induction a as [|a IHa].
- intros;reflexivity.
- unfold mult;simpl;change nat_mult with mult.
  intros b c.
  rewrite (mul_comm (_ + _) c).
  rewrite add_mul_distr_l.
  rewrite (mul_comm c (a*b)).
  rewrite <-IHa. rewrite (mul_comm b c). reflexivity.
Qed.

Instance: SemiRing nat.
Proof.
repeat (split; try apply _);
first [change sg_op with plus; change mon_unit with 0
      |change sg_op with mult; change mon_unit with 1].
- exact add_0_r.
- exact add_0_r.
- hnf;simpl_nat. intros a.
  rewrite mul_S_r,mul_0_r. apply add_0_r.
Qed.

(* misc *)
Instance S_neq_0 x : PropHolds (~ S x = 0).
Proof.
intros E.
change ((fun a => match a with S _ => True | 0 => False end) 0).
transport E. split.
Qed.

Definition pred x := match x with | 0 => 0 | S k => k end.

Instance: Injective S := { injective := fun a b E => ap pred E }.

Global Instance nat_dec: DecidablePaths nat.
Proof.
hnf. intros a;induction a as [|a IHa].
- intros [|b].
  + left;reflexivity.
  + right;apply symmetric_neq,S_neq_0.
- intros [|b].
  + right;apply S_neq_0.
  + destruct (IHa b).
    * left. apply ap;trivial.
    * right;intros E. apply (injective S) in E. auto.
Defined.

(* Add Ring nat: (rings.stdlib_semiring_theory nat). *)

Close Scope nat_scope.

Instance: NaturalsToSemiRing nat :=
  λ _ _ _ _ _, fix f (n: nat) := match n with 0%nat => 0 | S n' => f n' + 1 end.

Section for_another_semiring.
  Context `{SemiRing R}.

  Notation toR := (naturals_to_semiring nat R).

(*   Add Ring R: (rings.stdlib_semiring_theory R). *)

  Let f_preserves_0: toR 0 = 0.
  Proof. reflexivity. Qed.

  Let f_preserves_1: toR 1 = 1.
  Proof.
  exact (plus_0_l _).
  Qed.

  Let f_preserves_plus a a': toR (a + a') = toR a + toR a'.
  Proof.
  induction a as [|a IHa].
  - change (toR a' = 0 + toR a').
    apply symmetry,plus_0_l.
  - change (toR (a + a') + 1 = toR (a) + 1 + toR a'). rewrite IHa.
    rewrite <-(plus_assoc _ 1), (plus_comm 1), plus_assoc.
    reflexivity.
  Qed.

  Let f_preserves_mult a a': toR (a * a') = toR a * toR a'.
  Proof.
  induction a as [|a IHa].
  - change (0 = 0 * toR a').
    rewrite mult_0_l. reflexivity.
  - change (toR (a' + a * a') = (toR a + 1) * toR a').
    rewrite f_preserves_plus, IHa.
    rewrite plus_mult_distr_r,mult_1_l.
    apply commutativity.
  Qed.

  Global Instance: SemiRing_Morphism (naturals_to_semiring nat R).
  Proof.
  repeat (split;try apply _);trivial.
  Qed.
End for_another_semiring.

Lemma O_nat_0 : O ≡ 0.
Proof. reflexivity. Qed.

Lemma S_nat_plus_1 x : S x ≡ x + 1.
Proof.
rewrite add_comm. reflexivity.
Qed.

Lemma S_nat_1_plus x : S x ≡ 1 + x.
Proof. reflexivity. Qed.

Lemma nat_induction (P : nat → Type) :
  P 0 → (∀ n, P n → P (1 + n)) → ∀ n, P n.
Proof nat_rect P.

Instance nat_naturals `{Funext} : Naturals nat.
Proof.
split;try apply _.
intros.
apply path_forall. red.
apply (nat_induction _).
+ change (0 = h 0).
  apply symmetry,preserves_0.
+ intros n E.
  change (naturals_to_semiring nat B n + 1 = h (1+n)).
  rewrite (add_comm 1).
  rewrite (preserves_plus (f:=h)).
  rewrite E. apply ap,symmetry,preserves_1.
Qed.

Lemma plus_eq_zero : forall a b : nat, a + b = 0 -> a = 0 /\ b = 0.
Proof.
intros [|];[intros [|];auto|].
intros ? E. destruct (S_neq_0 _ E).
Qed.

Lemma mult_eq_zero : forall a b : nat, a * b = 0 -> a = 0 \/ b = 0.
Proof.
intros [|] [|];auto.
simpl_nat.
intros E.
apply plus_eq_zero in E.
destruct (S_neq_0 _ (fst E)).
Qed.

Instance: NoZeroDivisors nat.
Proof.
intros x [Ex [y [Ey1 Ey2]]].
apply mult_eq_zero in Ey2.
destruct Ey2;auto.
Qed.

Instance: forall z:nat, LeftCancellation plus z.
Proof.
red. intros a;induction a as [|a IHa];simpl_nat;intros b c E.
- trivial.
- apply IHa. apply (injective S). assumption.
Qed.

Instance: ∀ z : nat, PropHolds (z ≠ 0) → LeftCancellation (.*.) z.
Proof.
unfold PropHolds. unfold LeftCancellation.
intros a Ea b c E;revert b c a Ea E.
induction b as [|b IHb];intros [|c];simpl_nat;intros a Ea E.
- reflexivity.
- rewrite mul_0_r in E.
  rewrite mul_S_r in E;apply symmetry in E.
  apply plus_eq_zero in E. destruct (Ea (fst E)).
- rewrite mul_0_r,mul_S_r in E. apply plus_eq_zero in E.
  destruct (Ea (fst E)).
- rewrite 2!mul_S_r in E.
  apply (left_cancellation _ _) in E.
  apply ap. apply IHb with a;trivial.
Qed.

(* Order *)
Instance nat_le: Le nat := Peano.le.
Instance nat_lt: Lt nat := Peano.lt.

Lemma le_plus : forall n k, n <= k + n.
Proof.
induction k.
- apply Peano.le_n.
- simpl_nat. constructor. assumption.
Qed.

Lemma le_exists : forall n m, n <= m <-> exists k, m = k + n.
Proof.
intros n m;split.
- intros E;induction E as [|m E IH].
  + exists 0;split.
  + destruct IH as [k IH].
    exists (S k). rewrite IH;reflexivity.
- intros [k Hk].
  rewrite Hk. apply le_plus.
Qed.

Lemma zero_least : forall a, 0 <= a.
Proof.
induction a;constructor;auto.
Qed.

Lemma le_S_S : forall a b, a <= b <-> S a <= S b.
Proof.
intros. etransitivity;[apply le_exists|].
etransitivity;[|apply symmetry,le_exists].
split;intros [k E];exists k.
- rewrite E,add_S_r. reflexivity.
- rewrite add_S_r in E;apply (injective _) in E. trivial.
Qed.

Lemma lt_0_S : forall a, 0 < S a.
Proof.
intros. apply le_S_S. apply zero_least.
Qed.

Lemma le_lt_dec : forall a b : nat, a <= b \/ b < a.
Proof.
induction a as [|a IHa].
- intros;left;apply zero_least.
- intros [|b].
  + right. apply lt_0_S.
  + destruct (IHa b).
    * left. apply le_S_S;trivial.
    * right. apply le_S_S. trivial.
Qed.

Lemma not_lt_0 : forall a, ~ a < 0.
Proof.
intros a E. apply le_exists in E.
destruct E as [k E].
apply symmetry,plus_eq_zero in E.
apply (S_neq_0 _ (snd E)).
Qed.

Lemma lt_le : forall a b, a < b -> a <= b.
Proof.
intros.
destruct b.
- destruct (not_lt_0 a). trivial.
- constructor. apply le_S_S. trivial.
Qed.

Local Instance : TotalRelation (_:Le nat).
Proof.
hnf. intros a b.
destruct (le_lt_dec a b);[left|right].
- trivial.
- apply lt_le;trivial.
Qed.

Local Instance: PartialOrder nat_le.
Proof.
repeat split.
- hnf;intros; constructor.
- hnf. intros a b c E1 E2.
  apply le_exists in E1;apply le_exists in E2.
  destruct E1 as [k1 E1], E2 as [k2 E2].
  rewrite E2,E1,add_assoc. apply le_plus.
- hnf. intros a b E1 E2.
  apply le_exists in E1;apply le_exists in E2.
  destruct E1 as [k1 E1], E2 as [k2 E2].
  assert (k1 + k2 = 0) as E.
  + apply (left_cancellation (+) a).
    rewrite plus_0_r.
    path_via (k2 + b).
    rewrite E1.
    rewrite (plus_comm a), (plus_assoc k2), (plus_comm k2).
    reflexivity.
  + apply plus_eq_zero in E. destruct E as [Ek1 Ek2].
    rewrite Ek2,plus_0_l in E2.
    trivial.
Qed.


Local Instance nat_strict : StrictOrder (_:Lt nat).
Proof.
split.
- hnf. intros x E.
  apply le_exists in E.
  destruct E as [k E].
  apply (S_neq_0 k).
  apply (left_cancellation (+) x).
  rewrite plus_0_r,add_S_r,<-add_S_l.
  rewrite add_comm. apply symmetry,E.
- hnf. intros a b c E1 E2.
  apply le_exists;apply le_exists in E1;apply le_exists in E2.
  destruct E1 as [k1 E1], E2 as [k2 E2].
  exists (S (k1+k2)).
  rewrite E2,E1.
  rewrite !add_S_r,add_S_l.
  rewrite (add_assoc k2), (add_comm k2).
  reflexivity.
Qed.


(*
Instance nat_apart : Apart nat := default_apart.
Instance nat_apartness : IsApart nat := dec_strong_setoid.
*)

Instance: is_mere_relation nat le.
Proof.
intros m n;apply Trunc.hprop_allpath.
generalize (idpath (S n)).
generalize n at 2 3 4 5.
change (forall n0 : nat,
S n = S n0 -> forall le_mn1 le_mn2 : m <= n0, le_mn1 = le_mn2).
induction (S n) as [|n0 IHn0].
- intros ? E;destruct (S_neq_0 _ (symmetry _ _ E)).
- clear n; intros n H.
  apply (injective S) in H.
  rewrite <- H; intros le_mn1 le_mn2; clear n H.
  pose (def_n2 := idpath n0);
  path_via (paths_ind n0 (fun n _ => le m _) le_mn2 n0 def_n2).
  generalize def_n2; revert le_mn1 le_mn2.
  generalize n0 at 1 4 5 8; intros n1 le_mn1.
  destruct le_mn1; intros le_mn2; destruct le_mn2.
  + intros def_n0.
    rewrite (Trunc.path_ishprop def_n0 idpath).
    simpl. reflexivity.
  + intros def_n0; generalize le_mn2; rewrite <-def_n0; intros le_mn0.
    destruct (irreflexivity nat_lt _ le_mn0).
  + intros def_n0.
    destruct (irreflexivity nat_lt m0).
    rewrite def_n0 in le_mn1;trivial.
  + intros def_n0. pose proof (injective S _ _ def_n0) as E.
    destruct E.
    rewrite (Trunc.path_ishprop def_n0 idpath). simpl.
    apply ap. auto.
Qed.

Instance nat_trichotomy : Trichotomy (lt:Lt nat).
Proof.
hnf.
intros a b. destruct (le_lt_dec a b) as [[|]|E];auto.
left. apply le_S_S. trivial.
Qed.

Instance nat_apart : Apart nat := fun n m => n < m \/ m < n.
Instance nat_trivial_apart : TrivialApart nat.
Proof.
split.
- intros;apply ishprop_sum;try apply _.
  intros E1 E2. apply (irreflexivity nat_lt x).
  transitivity y;trivial.
- intros a b;split;intros E.
  + destruct E as [E|E];apply irrefl_neq in E;trivial.
    apply symmetric_neq;trivial.
  + hnf. destruct (trichotomy _ a b) as [?|[?|?]];auto.
    destruct E;trivial.
Qed.

Fail Definition bob := @dec_strict_pseudo_order
  nat nat_lt nat_strict nat_apart nat_trivial_apart _ nat_trichotomy.

(*
Instance nat_full : FullPseudoSemiRingOrder nat_le nat_lt.
Proof.
split;[split|]. 
- exact bob. refine dec_strict_pseudo_order.

STOP.

repeat (split;try apply _).
assert (SemiRingOrder nat_le).
 repeat (split; try apply _).
    intros x y E. exists (y - x)%nat. now apply le_plus_minus.
   intros. now apply Plus.plus_le_compat_l.
  intros. now apply plus_le_reg_l with z.
 intros x y ? ?. change (0 * 0 <= x * y)%nat. now apply Mult.mult_le_compat.
apply dec_full_pseudo_srorder.
now apply Nat.le_neq.
Qed.

Instance: OrderEmbedding S.
Proof. repeat (split; try apply _). exact le_n_S. exact le_S_n. Qed.

Instance: StrictOrderEmbedding S.
Proof. split; try apply _. Qed.
 *)

Lemma nat_lt_not_le : forall a b : nat, a < b -> ~ b <= a.
Proof.
intros a b E1 E2.
apply le_exists in E1;apply le_exists in E2.
destruct E1 as [k1 E1], E2 as [k2 E2].
apply (S_neq_0 (k1 + k2)).
apply (left_cancellation (+) a).
rewrite plus_0_r.
rewrite E1 in E2.
rewrite add_S_r;rewrite !add_S_r in E2.
rewrite (add_assoc a), (add_comm a), <-(add_assoc k1), (add_comm a).
rewrite (add_assoc k1), (add_comm k1), <-(add_assoc k2).
apply symmetry,E2.
Qed.

Instance nat_le_dec: Decision (x ≤ y).
Proof.
intros a b. destruct (le_lt_dec a b).
- left;trivial.
- right. apply nat_lt_not_le. trivial.
Qed.
(* 
Instance nat_cut_minus: CutMinus nat := minus.
Instance: CutMinusSpec nat nat_cut_minus.
Proof.
  split.
   symmetry. rewrite commutativity.
   now apply le_plus_minus.
  intros x y E. destruct (orders.le_equiv_lt x y E) as [E2|E2].
   rewrite E2. now apply minus_diag.
  apply not_le_minus_0. now apply orders.lt_not_le_flip.
Qed.
 *)