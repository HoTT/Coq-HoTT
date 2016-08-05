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

Definition IsTop (s : Sier) : Type0 := top <= s.
Coercion IsTop : Sier >-> Sortclass.

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

Lemma top_le_meet : forall a b : Sier, meet a b <-> a /\ b.
Proof.
unfold IsTop. intros a b;split.
- intros E;split;transitivity (meet a b);trivial.
  + apply meet_lb_l.
  + apply meet_lb_r.
- intros [E1 E2]. apply meet_le;trivial.
Qed.

Lemma top_le_join : forall a b : Sier, join a b <-> hor a b.
Proof.
unfold IsTop. intros a b;split.
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

Lemma top_le_joined_seq_n : forall f n, joined_seq f n <->
  merely (exists m, m <= n /\ f m).
Proof.
unfold IsTop. intros f;induction n as [|n IHn];simpl;
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

Lemma top_le_sup : forall (s : IncreasingSequence Sier),
  IsTop (sup Unit s) <-> merely (exists n, s n).
Proof.
intros s;split.
- intros E. apply (eta_le_sup _) in E.
  exact E.
- apply (Trunc_ind _);intros [n E].
  red;transitivity (s n);trivial.
  apply sup_is_ub.
Qed.

Lemma top_le_countable_sup : forall f, CountableSup f <->
  merely (exists n, f n).
Proof.
unfold IsTop. intros f;split.
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

Lemma countable_sup_meet_distr_r : forall a f,
  meet (CountableSup f) a = CountableSup (fun n => meet (f n) a).
Proof.
intros a f.
unfold CountableSup at 1. rewrite SierMeet_sup.
apply sup_extensionality.
induction n as [|n IHn];simpl.
- reflexivity.
- simpl in IHn. rewrite <-IHn.
  apply meet_join_distr_r.
Qed.

Lemma countable_sup_meet_distr_l : forall a f,
  meet a (CountableSup f) = CountableSup (fun n => meet a (f n)).
Proof.
intros. rewrite (commutativity (f:=meet)),countable_sup_meet_distr_r.
apply ap,path_forall. intros n. apply commutativity.
Qed.

Section enumerable_sup.
Variable A : Type.

Context `{Enumerable A}.

Definition EnumerableSup (f : A -> Sier)  : Sier
  := CountableSup (f ∘ (enumerator A)).

Lemma enumerable_sup_ub : forall f x, f x <= EnumerableSup f.
Proof.
intros f x.
generalize (center _ (enumerator_issurj _ x)). apply (Trunc_ind _).
intros [a []]. clear x. unfold EnumerableSup.
apply (countable_sup_ub (compose _ _) a).
Qed.

Lemma enumerable_sup_least_ub : forall f s, (forall x, f x <= s) ->
  EnumerableSup f <= s.
Proof.
intros f s E. apply countable_sup_least_ub.
intros;apply E.
Qed.

Lemma top_le_enumerable_sup : forall f, EnumerableSup f <->
  merely (exists x, f x).
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

Lemma enumerable_sup_meet_distr_l : forall a f,
  meet a (EnumerableSup f) = EnumerableSup (fun n => meet a (f n)).
Proof.
intros. apply countable_sup_meet_distr_l.
Qed.

Lemma enumerable_sup_meet_distr_r : forall a f,
  meet (EnumerableSup f) a = EnumerableSup (fun n => meet (f n) a).
Proof.
intros. apply countable_sup_meet_distr_r.
Qed.

End enumerable_sup.

Lemma not_bot : ~ (@bottom Sier _).
Proof.
intros E.
pose proof @trunc_contr@{Set Set} as trunc_contr.
apply (not_eta_le_bot@{Set} _ tt). apply E.
Qed.

Definition DecSier (A : Type) `{Decidable A} : Sier
  := match decide A with | inl _ => top | inr _ => bottom end.

Lemma dec_sier_top `{Decidable A} : A -> DecSier A = top.
Proof.
intros E. unfold DecSier. destruct (decide A) as [?|E'];trivial.
destruct (E' E).
Qed.

Lemma dec_sier_bot `{Decidable A} : ~ A -> DecSier A = bottom.
Proof.
intros E'. unfold DecSier. destruct (decide A) as [E|?];trivial.
destruct (E' E).
Qed.

Lemma dec_sier_pr : forall A `{Decidable A},
  A <-> DecSier A.
Proof.
intros A ?. split.
- intros E. rewrite (dec_sier_top E). apply top_greatest.
- unfold DecSier. destruct (decide A) as [E|E];intros E'.
  + trivial.
  + destruct (not_bot E').
Qed.

Lemma SierLe_imply : forall a b : Sier, a <= b -> a -> b.
Proof.
intros a b E E';red;transitivity a;trivial.
Qed.

Definition meet_top_l : forall a : Sier, meet top a = a
  := fun _ => idpath.

Lemma meet_top_r : forall a : Sier, meet a top = a.
Proof.
intros. etransitivity;[|apply meet_top_l]. apply commutativity.
Qed.

Definition meet_bot_l : forall a : Sier, meet bottom a = bottom
  := fun _ => idpath.

Lemma meet_bot_r : forall a : Sier, meet a bottom = bottom.
Proof.
intros. etransitivity;[|apply meet_bot_l]. apply commutativity.
Qed.

Definition join_top_l : forall a : Sier, join top a = top
  := fun _ => idpath.

Lemma join_top_r : forall a : Sier, join a top = top.
Proof.
intros. etransitivity;[|apply join_top_l]. apply commutativity.
Qed.

Definition join_bot_l : forall a : Sier, join bottom a = a
  := fun _ => idpath.

Lemma join_bot_r : forall a : Sier, join a bottom = a.
Proof.
intros. etransitivity;[|apply join_bot_l]. apply commutativity.
Qed.

Lemma dec_sier_meet_le A `{Decidable A}
  : forall b c, meet (DecSier A) b <= c <-> (A -> b <= c).
Proof.
intros. split.
- intros E Ea. rewrite (dec_sier_top Ea),meet_top_l in E. trivial.
- intros E. destruct (decide A) as [Ea|Ea].
  + rewrite (dec_sier_top Ea),meet_top_l. auto.
  + rewrite (dec_sier_bot Ea),meet_bot_l. apply bot_least.
Qed.

Lemma top_le_eq : forall a : Sier, a -> a = top.
Proof.
intros a E. apply (antisymmetry le);trivial.
apply top_greatest.
Qed.

Lemma bot_eq : forall a : Sier, a <= bottom -> a = bottom.
Proof.
intros a E. apply (antisymmetry le);trivial.
apply bot_least.
Qed.

Lemma dec_sier_meet A `{Decidable A} B `{Decidable B}
  : meet (DecSier A) (DecSier B) = DecSier (A /\ B).
Proof.
unfold DecSier at 1 2.
destruct (decide A) as [E1|E1], (decide B) as [E2|E2];
rewrite ?meet_top_l,?meet_bot_l;Symmetry;
first [apply dec_sier_top | apply dec_sier_bot];auto;intros [E3 E4];auto.
Qed.

Lemma dec_sier_join A `{Decidable A} B `{Decidable B}
  : join (DecSier A) (DecSier B) = DecSier (A \/ B).
Proof.
unfold DecSier at 1 2.
destruct (decide A) as [E1|E1], (decide B) as [E2|E2];
rewrite ?join_top_l,?join_bot_l;Symmetry;
first [apply dec_sier_top | apply dec_sier_bot];auto;intros [E3|E3];auto.
Qed.

Lemma dec_sier_le_imply A `{Decidable A} : forall b : Sier,
  (A -> b) -> DecSier A <= b.
Proof.
intros b E. unfold DecSier. destruct (decide A) as [E1|E1].
- apply E. trivial.
- apply bot_least.
Qed.

Lemma imply_le : forall a b : Sier, (a -> b) -> a <= b.
Proof.
apply (partial_ind0 _ (fun a => forall b, _ -> _)).
- intros [] b E. apply E. apply top_greatest.
- intros;apply bot_least.
- intros s IH b E. apply sup_le_r. intros n.
  apply IH. intros En. apply E.
  apply top_le_sup. apply tr;exists n;trivial.
Qed.

End contents.
