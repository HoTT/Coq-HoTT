Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.HSet
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.orders.lattices
  HoTTClasses.theory.lattices
  HoTTClasses.implementations.partiality
  HoTTClasses.implementations.peano_naturals.

Local Set Universe Minimization ToSet.

Definition Sier := partial Unit.

Global Instance SierLe : Le Sier := _.
Arguments SierLe _ _ /.

Global Instance SierBot : Bottom Sier := bot _.

Global Instance SierTop : Top Sier := eta _ tt.

Section contents.
Context `{Funext} `{Univalence}.

Instance Sier_order : PartialOrder SierLe := partial_order _.

Lemma top_greatest : forall x : Sier, x <= top.
Proof.
apply (partial_ind0 _ _).
- intros [];reflexivity.
- apply bot_least.
- intros f IH. apply sup_le_r. exact IH.
Qed.

(* We need this for the bot_least case. *)
Definition SierJoin_aux : forall y : Sier, Sier -> sigT (fun j : Sier => y <= j).
Proof.
intros y. apply (partial_rec Unit _ (fun a b => a.1 <= b.1)).
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
- intros _;exists top. apply top_greatest.
- exists y;reflexivity.
- intros f IH. simpl in IH. simple refine (existT _ _ _);simpl.
  + apply sup. exists (fun n => (f n).1).
    exact IH.
  + transitivity ((f O).1).
    * apply ((f O).2).
    * exact (sup_is_ub _ {| seq := λ n : nat, (f n).1; seq_increasing := IH |} O).
- intros;reflexivity.
- simpl. apply pr2.
- simpl. intros s p x. apply sup_le_l.
- simpl. intros s p x IH. apply sup_le_r.
  apply IH.
- intros a b E1 E2. apply Sigma.path_sigma_hprop.
  apply (antisymmetry le);trivial.
Defined.

Global Instance SierJoin : Join Sier
  := fun x y => (SierJoin_aux y x).1.

Definition SierJoin_top : forall x : Sier, join top x = top
  := fun _ => idpath.

Definition SierJoin_bot : forall x : Sier, join bottom x = x
  := fun _ => idpath.

Instance SierJoin_preserve_le_l : forall y, OrderPreserving (fun x => join x y)
  := fun y => partialLe_rec _ _ (fun a b => a.1 <= b.1) _.

Definition SierJoin_seq_l : IncreasingSequence Sier -> Sier ->
  IncreasingSequence Sier.
Proof.
intros s y;exists (fun n => join (s n) y).
intros n;apply (order_preserving (fun x => join x y)). apply seq_increasing.
Defined.

Definition SierJoin_sup : forall s (y : Sier),
  join (sup _ s) y = sup _ (SierJoin_seq_l s y)
  := fun _ _ => idpath.

Definition SierJoin_ub_r : forall x y : Sier, y <= join x y
  := fun x y => (SierJoin_aux y x).2.

Instance SierJoin_is_join : JoinSemiLatticeOrder SierLe.
Proof.
split.
- apply _.
- intros x y;revert x;apply (partial_ind0 _ _).
  + intros [];reflexivity.
  + apply bot_least.
  + intros s IH. apply sup_le_r.
    intros n. change (join (sup Unit s) y) with (sup Unit (SierJoin_seq_l s y)).
    etransitivity;[apply IH|].
    exact (sup_is_ub _ (SierJoin_seq_l s y) _).
- apply SierJoin_ub_r.
- apply (partial_ind0 _ (fun x => forall y z, _ -> _ -> _)).
  + intros [] y z E1 E2. apply E1.
  + intros y z E1 E2. apply E2.
  + intros s IH y z E1 E2.
    apply (sup_le_r _ (SierJoin_seq_l s y)).
    intros n. apply IH;trivial.
    apply sup_le_l. trivial.
Qed.

Global Instance SierMeet : Meet Sier.
Proof.
intros x y;revert x;apply (partial_rec Unit _ le).
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
- intros _;exact y.
- exact bottom.
- intros f IH;simpl in IH.
  apply sup. exists f. exact IH.
- reflexivity.
- apply bot_least.
- intros s p x IH;apply (sup_le_l _ _ _ IH).
- intros s p x IH;apply sup_le_r. apply IH.
Defined.

Definition SierMeet_top : forall x : Sier, meet top x = x
  := fun _ => idpath.

Definition SierMeet_bot : forall x : Sier, meet bottom x = bottom
  := fun _ => idpath.

Instance SierMeet_preserve_le_l : forall y, OrderPreserving (fun x => meet x y)
  := fun y => partialLe_rec _ _ le _.

Definition SierMeet_seq_l : IncreasingSequence Sier -> Sier ->
  IncreasingSequence Sier.
Proof.
intros s y;exists (fun n => meet (s n) y).
intros n;apply (order_preserving (fun x => meet x y)). apply seq_increasing.
Defined.

Definition SierMeet_sup : forall s (y : Sier),
  meet (sup _ s) y = sup _ (SierMeet_seq_l s y)
  := fun _ _ => idpath.

Instance SierMeet_is_meet : MeetSemiLatticeOrder SierLe.
Proof.
split.
- apply _.
- apply (partial_ind0 _ (fun x => forall y, _)).
  + intros [] y. apply top_greatest.
  + intros;apply bot_least.
  + intros s IH y.
    change (sup Unit s ⊓ y) with (sup _ (SierMeet_seq_l s y)).
    apply sup_le_r. intros n. simpl.
    etransitivity;[apply IH|]. apply sup_is_ub.
- apply (partial_ind0 _ (fun x => forall y, _)).
  + intros; reflexivity.
  + apply bot_least.
  + intros s IH y.
    change (sup Unit s ⊓ y) with (sup _ (SierMeet_seq_l s y)).
    apply sup_le_r. simpl. intros n;apply IH.
- apply (partial_ind0 _ (fun x => forall y z, _ -> _ -> _)).
  + intros [] y z E1 E2. apply E2.
  + intros y z E1 E2. apply E1.
  + intros s IH y z;revert z y.
    apply (partial_ind0 _ (fun z => forall y, _ -> _ -> _)).
    * intros [] y E1 E2. apply (eta_le_sup _) in E1.
      revert E1;apply (Trunc_ind _);intros [n E1].
      transitivity (meet (s n) y);auto.
      exact (sup_is_ub _ (SierMeet_seq_l _ _) _).
    * intros;apply bot_least.
    * intros s' IH' y E1 E2.
      apply sup_le_r. intros n.
      apply IH';(transitivity (sup _ s');[apply sup_is_ub|]);trivial.
Qed.

Global Instance Sier_lattice_order : LatticeOrder SierLe := {}.
Local Existing Instance join_sl_order_join_sl.
Local Existing Instance meet_sl_order_meet_sl.

Fixpoint joined_seq_aux (f : nat -> Sier) (n : nat) : Sier :=
  match n with
  | O => f O
  | S k => join (joined_seq_aux f k) (f n)
  end.

Definition joined_seq (f : nat -> Sier) : IncreasingSequence Sier.
Proof.
exists (joined_seq_aux f).
intros;simpl. apply join_ub_l.
Defined.

Definition CountableSup (f : nat -> Sier) : Sier
  := sup _ (joined_seq f).

Lemma joined_seq_ub_n : forall f n, f n <= joined_seq f n.
Proof.
intros f [|n].
- reflexivity.
- simpl. apply join_ub_r.
Qed.

Lemma countable_sup_ub : forall f n, f n <= CountableSup f.
Proof.
intros. transitivity (joined_seq f n).
- apply joined_seq_ub_n.
- unfold CountableSup. apply sup_is_ub.
Qed.

Lemma joined_seq_least_ub_n : forall f n x, (forall m, m <= n -> f m <= x) ->
  joined_seq f n <= x.
Proof.
intros f;induction n as [|n IHn];intros x E.
- simpl. apply E. reflexivity.
- simpl. apply join_le.
  + apply IHn. intros m Em;apply E.
    constructor;trivial.
  + apply E. reflexivity.
Qed.

Lemma countable_sup_least_ub : forall f x, (forall n, f n <= x) ->
  CountableSup f <= x.
Proof.
intros f x E. apply sup_le_r.
intros n. apply joined_seq_least_ub_n. intros m _;apply E.
Defined.

Lemma top_le_meet : forall a b, top <= meet a b <-> top <= a /\ top <= b.
Proof.
intros a b;split.
- intros E;split;transitivity (meet a b);trivial.
  + apply meet_lb_l.
  + apply meet_lb_r.
- intros [E1 E2]. apply meet_le;trivial.
Qed.

Lemma top_le_join : forall a b, top <= join a b <-> hor (top <= a) (top <= b).
Proof.
intros a b;split.
- revert a b;apply (partial_ind0 _ (fun a => forall b, _ -> _)).
  + intros [] ? E;apply tr;left;apply E.
  + intros b E;apply tr;right;apply E.
  + intros s IH b E.
    change (top <= sup _ (SierJoin_seq_l s b)) in E.
    apply (eta_le_sup _) in E. revert E. apply (Trunc_ind _).
    intros [n E]. simpl in E.
    apply IH in E. revert E;apply (Trunc_ind _).
    intros [E|E];apply tr;[left|right;trivial].
    transitivity (s n);trivial. apply sup_is_ub.
- apply (Trunc_ind _);intros [E|E].
  + transitivity a;auto. apply join_ub_l.
  + transitivity b;auto. apply join_ub_r.
Qed.

Lemma top_le_joined_seq_n : forall f n, top <= joined_seq f n <->
  merely (exists m, m <= n /\ top <= f m).
Proof.
intros f;induction n as [|n IHn];simpl;
(split;[intros E|apply (Trunc_ind _);intros [m [Em E]]]).
- apply tr;exists 0;split;trivial. reflexivity.
- rewrite (antisymmetry le m 0 Em (zero_least m)) in E. trivial.
- apply top_le_join in E. revert E;apply (Trunc_ind _);intros [E|E].
  + apply IHn in E;revert E;apply (Trunc_ind _);intros [m [E1 E2]].
    apply tr;exists m;split;trivial. constructor;trivial.
  + apply tr;exists (S n);split;trivial. reflexivity.
- apply le_S_either in Em. destruct Em as [Em|Em].
  + transitivity (joined_seq f n);[|apply join_ub_l].
    apply IHn. apply tr;exists m;auto.
  + rewrite <-Em. transitivity (f m);auto. apply join_ub_r.
Qed.

Lemma top_le_countable_sup : forall f, top <= CountableSup f <->
  merely (exists n, top <= f n).
Proof.
intros f;split.
- intros E. apply (eta_le_sup _) in E.
  revert E;apply (Trunc_ind _);intros [n E].
  apply top_le_joined_seq_n in E. revert E;apply (Trunc_ind _);intros [m [_ E]].
  apply tr;exists m;trivial.
- apply (Trunc_ind _);intros [n E].
  transitivity (f n);trivial. apply countable_sup_ub.
Qed.

Global Instance Sier_distributive_lattice : DistributiveLattice Sier.
Proof.
repeat (split;try apply _).
- hnf. intros a b. apply (antisymmetry le).
  + apply join_le.
    * reflexivity.
    * apply meet_lb_l.
  + apply join_ub_l.
- hnf. intros a b. apply (antisymmetry le).
  + apply meet_lb_l.
  + apply meet_le.
    * reflexivity.
    * apply join_ub_l.
- hnf. intros a b c. apply (antisymmetry le).
  + apply join_le; apply meet_le.
    * apply join_ub_l.
    * apply join_ub_l.
    * transitivity b.
      { apply meet_lb_l. }
      { apply join_ub_r. }
    * transitivity c.
      { apply meet_lb_r. }
      { apply join_ub_r. }
  + revert a b c. apply (partial_ind0 _ (fun a => forall b c, _)).
    * intros [] b c. reflexivity.
    * reflexivity.
    * intros s IH b c.
      rewrite !SierJoin_sup,SierMeet_sup.
      apply sup_le_r. intros n.
      simpl. rewrite (commutativity (f:=meet)),SierMeet_sup;simpl.
      apply sup_le_r;intros m.
      simpl.
      assert (E : exists k, n <= k /\ m <= k)
      by (destruct (total le n m) as [E|E];eauto).
      destruct E as [k [En Em]].
      etransitivity;[|apply (sup_is_ub _ _ k)].
      simpl. etransitivity;[|apply IH].
      apply meet_le.
      { etransitivity;[apply meet_lb_r|].
        apply join_le;[|apply join_ub_r].
        transitivity (s k);[|apply join_ub_l].
        apply (order_preserving s). trivial. }
      { etransitivity;[apply meet_lb_l|].
        apply join_le;[|apply join_ub_r].
        transitivity (s k);[|apply join_ub_l].
        apply (order_preserving s). trivial. }
Qed.

Lemma top_le_countable_sup_meet : forall f g,
  top <= CountableSup (fun n => meet (f n) (g n)) ->
  top <= meet (CountableSup f) (CountableSup g).
Proof.
intros f g E. apply top_le_countable_sup in E.
revert E;apply (Trunc_ind _);intros [n E].
apply top_le_meet in E.
apply top_le_meet;split;apply top_le_countable_sup,tr;exists n;apply E.
Qed.

Section enumerable_sup.
Variable A : Type.

Context `{Enumerable A}.

Definition EnumerableSup (f : A -> Sier)  : Sier
  := CountableSup (f ∘ (enumerator A)).

Lemma enumerable_sub_ub : forall f x, f x <= EnumerableSup f.
Proof.
intros f x.
generalize (center _ (enumerator_issurj _ x)). apply (Trunc_ind _).
intros [a []]. clear x. unfold EnumerableSup.
apply (countable_sup_ub (compose _ _) a).
Qed.

Lemma enumerable_sub_least_ub : forall f s, (forall x, f x <= s) ->
  EnumerableSup f <= s.
Proof.
intros f s E. apply countable_sup_least_ub.
intros;apply E.
Qed.

Lemma top_le_enumerable_sub : forall f, top <= EnumerableSup f <->
  merely (exists x, top <= f x).
Proof.
intros f;split.
- intros E. apply top_le_countable_sup in E;revert E;
  apply (Trunc_ind _);intros [n E].
  apply tr;econstructor;apply E.
- apply (Trunc_ind _);intros [x E].
  generalize (center _ (enumerator_issurj _ x)). apply (Trunc_ind _).
  intros [a Ea]. destruct Ea.
  apply top_le_countable_sup. apply tr;exists a;apply E.
Qed.

End enumerable_sup.

End contents.
