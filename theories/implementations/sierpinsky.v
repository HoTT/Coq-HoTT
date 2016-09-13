Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.HSet
  HoTT.Basics.PathGroupoids
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

Lemma SierMeet_is_meet@{} : MeetSemiLatticeOrder SierLe.
Proof.
split.
- apply _.
- intros x y;revert x. apply (partial_ind0 _ _).
  + intros []. apply top_greatest.
  + intros;apply bot_least.
  + intros s IH.
    change (sup Unit s ⊓ y) with (sup _ (SierMeet_seq_l s y)).
    apply sup_le_r. intros n. simpl.
    etransitivity;[apply IH|]. apply sup_is_ub.
- intros x y;revert x. apply (partial_ind0 _ _).
  + reflexivity.
  + apply bot_least.
  + intros s IH.
    change (sup Unit s ⊓ y) with (sup _ (SierMeet_seq_l s y)).
    apply sup_le_r. simpl. intros n;apply IH.
- apply (partial_ind0 _ (fun x => forall y z, _ -> _ -> _)).
  + intros [] y z E1 E2. apply E2.
  + intros y z E1 E2. apply E1.
  + intros s IH y z;revert z y.
    apply (partial_ind0 _ (fun z => forall y, _ -> _ -> _)).
    * intros [] y E1 E2. pose proof @trunc_contr@{Set Set} as trunc_contr.
      apply (eta_le_sup _) in E1.
      revert E1;apply (Trunc_ind _);intros [n E1].
      transitivity (meet (s n) y);auto.
      exact (sup_is_ub _ (SierMeet_seq_l _ _) _).
    * intros;apply bot_least.
    * intros s' IH' y E1 E2.
      apply sup_le_r. intros n.
      apply IH';(transitivity (sup _ s');[apply sup_is_ub|]);trivial.
Qed.
Existing Instance SierMeet_is_meet.

Section distrib_lattice.

Local Instance Sier_lattice_order : LatticeOrder SierLe := {}.
Local Existing Instance join_sl_order_join_sl.
Local Existing Instance meet_sl_order_meet_sl.

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

End distrib_lattice.
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

Lemma joined_seq_least_ub_n' : forall f n x, (forall m, m <= n -> f m <= x) ->
  joined_seq f n <= x.
Proof.
intros f;induction n as [|n IHn];intros x E.
- simpl. apply E. reflexivity.
- simpl. apply join_le.
  + apply IHn. intros m Em;apply E.
    constructor;trivial.
  + apply E. reflexivity.
Qed.

Definition joined_seq_least_ub_n@{} := joined_seq_least_ub_n'@{Set Ularge Set}.

Lemma countable_sup_least_ub : forall f x, (forall n, f n <= x) ->
  CountableSup f <= x.
Proof.
intros f x E. apply sup_le_r.
intros n. apply joined_seq_least_ub_n. intros m _;apply E.
Qed.

Lemma top_le_meet : forall a b : Sier, meet a b <-> a /\ b.
Proof.
unfold IsTop. intros a b;split.
- intros E;split;transitivity (meet a b);trivial.
  + apply meet_lb_l.
  + apply meet_lb_r.
- intros [E1 E2]. apply meet_le;trivial.
Qed.

Lemma top_le_join@{} : forall a b : Sier, join a b <-> hor a b.
Proof.
unfold IsTop. intros a b;split.
- revert a b;apply (partial_ind0 _ (fun a => forall b, _ -> _)).
  + intros [] ? E;apply tr;left;apply E.
  + intros b E;apply tr;right;apply E.
  + intros s IH b E.
    change (top <= sup _ (SierJoin_seq_l s b)) in E.
    pose proof @trunc_contr@{Set Set} as trunc_contr.
    apply (eta_le_sup _) in E. revert E. apply (Trunc_ind _).
    intros [n E]. simpl in E.
    apply IH in E. revert E;apply (Trunc_ind _).
    intros [E|E];apply tr;[left|right;trivial].
    transitivity (s n);trivial. apply sup_is_ub.
- apply (Trunc_ind _);intros [E|E].
  + transitivity a;auto. apply join_ub_l.
  + transitivity b;auto. apply join_ub_r.
Qed.

Lemma top_le_joined_seq_n' : forall f n, joined_seq f n <->
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

Definition top_le_joined_seq_n@{} := top_le_joined_seq_n'@{Set Ularge Set Set}.

Lemma top_le_sup@{} : forall (s : IncreasingSequence Sier),
  IsTop (sup Unit s) <-> merely@{Set} (exists n, s n).
Proof.
intros s;split.
- intros E. pose proof @trunc_contr@{Set Set} as trunc_contr.
  apply (eta_le_sup _) in E.
  exact E.
- apply (Trunc_ind _);intros [n E].
  red;transitivity (s n);trivial.
  apply sup_is_ub.
Qed.

Lemma top_le_countable_sup@{} : forall f, CountableSup f <->
  merely (exists n, f n).
Proof.
unfold IsTop. intros f;split.
- intros E. pose proof @trunc_contr@{Set Set} as trunc_contr;
  apply (eta_le_sup _) in E.
  revert E;apply (Trunc_ind _);intros [n E].
  apply top_le_joined_seq_n in E. revert E;apply (Trunc_ind _);intros [m [_ E]].
  apply tr;exists m;trivial.
- apply (Trunc_ind _);intros [n E].
  transitivity (f n);trivial. apply countable_sup_ub.
Qed.

Lemma countable_sup_meet_distr_r : forall a f,
  meet (CountableSup f) a = CountableSup (fun n => meet (f n) a).
Proof.
intros a f.
unfold CountableSup at 1. rewrite SierMeet_sup.
apply sup_extensionality;simpl.
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
Universe UA.
Variable A : Type@{UA}.

Context `{Enumerable A}.

Definition EnumerableSup@{} (f : A -> Sier)  : Sier
  := CountableSup (f ∘ (enumerator A)).

Lemma enumerable_sup_ub' : forall (f:A->Sier) (x:A), f x <= EnumerableSup f.
Proof.
intros f x.
generalize (center _ (enumerator_issurj _ x)). apply (Trunc_ind _).
intros [a []]. clear x. unfold EnumerableSup.
apply (countable_sup_ub (compose _ _) a).
Qed.

Definition enumerable_sup_ub@{} := enumerable_sup_ub'@{Uhuge Ularge}.

Lemma enumerable_sup_least_ub@{} : forall (f:A->Sier) s, (forall x, f x <= s) ->
  EnumerableSup f <= s.
Proof.
intros f s E. apply countable_sup_least_ub.
intros;apply E.
Qed.

Lemma top_le_enumerable_sup' : forall f, iff@{Set UA UA} (EnumerableSup f)
  (merely (exists x, f x)).
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

Definition top_le_enumerable_sup@{} := top_le_enumerable_sup'@{Uhuge Ularge}.

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

Lemma imply_le : forall a b : Sier, (a -> b) -> a <= b.
Proof.
apply (partial_ind0 _ (fun a => forall b, _ -> _)).
- intros [] b E. apply E. apply top_greatest.
- intros;apply bot_least.
- intros s IH b E. apply sup_le_r. intros n.
  apply IH. intros En. apply E.
  red. transitivity (s n);trivial. apply sup_is_ub.
Qed.

Class SemiDecide@{i} (A : Type@{i}) := semi_decide : Sier.
Arguments semi_decide A {_}.

Class SemiDecidable@{i} (A : Type@{i}) `{SemiDecide A}
  := semi_decidable : iff@{Set i i} (semi_decide A) A.

Global Instance decidable_semi_decide@{i} (A:Type@{i}) `{Decidable A}
  : SemiDecide A.
Proof.
red. exact (if decide A then top else bottom).
Defined.
Arguments decidable_semi_decide _ {_} /.

Global Instance decidable_semi_decidable@{i} (A:Type@{i}) `{Decidable A}
  : SemiDecidable@{i} A.
Proof.
red. unfold semi_decide;simpl. destruct (decide A) as [E|E];split;intros E'.
- trivial.
- apply top_greatest.
- apply not_bot in E'. destruct E'.
- destruct (E E').
Qed.

Lemma semidecidable_top@{i} {A:Type@{i} } `{SemiDecidable@{i} A}
  : A -> semi_decide A = top.
Proof.
intros E. apply top_le_eq. apply semi_decidable. trivial.
Qed.

Lemma semidecidable_bot@{i} {A:Type@{i} } `{SemiDecidable@{i} A}
  : ~ A -> semi_decide A = bottom.
Proof.
intros E'. apply bot_eq,imply_le. intros E. apply semi_decidable in E.
destruct (E' E).
Qed.

Lemma semi_decide_meet_le@{i} (A:Type@{i}) `{SemiDecidable@{i} A}
  : forall b c, iff@{Set i i} (meet (semi_decide A) b <= c) (A -> b <= c).
Proof.
intros. split.
- intros E Ea. rewrite (semidecidable_top Ea),meet_top_l in E. trivial.
- intros E. apply imply_le;intros E'.
  apply top_le_meet in E';destruct E' as [E1 E2].
  apply semi_decidable in E1. apply SierLe_imply with b;trivial.
  apply E;trivial.
Qed.

Global Instance semi_decide_conj@{i j k} (A:Type@{i}) `{SemiDecide A}
  (B:Type@{j}) `{SemiDecide B}
  : SemiDecide@{k} (A /\ B)
  := meet (semi_decide A) (semi_decide B).
Arguments semi_decide_conj _ {_} _ {_} /.

Global Instance semi_decidable_conj@{i j k} (A:Type@{i}) `{SemiDecidable@{i} A}
  (B:Type@{j}) `{SemiDecidable@{j} B}
  : SemiDecidable@{k} (A /\ B).
Proof.
split.
- intros E;apply top_le_meet in E;destruct E as [E1 E2];
  apply semi_decidable in E1;apply semi_decidable in E2;split;trivial.
- intros [E1 E2];apply top_le_meet;split;apply semi_decidable;trivial.
Qed.

Global Instance semi_decide_disj@{i j k} (A:Type@{i}) `{SemiDecide@{i} A}
  (B:Type@{j}) `{SemiDecide@{j} B}
  : SemiDecide@{k} (hor@{i j k} A B)
  := join (semi_decide A) (semi_decide B).
Arguments semi_decide_disj _ {_} _ {_} /.

Global Instance semi_decidable_disj@{i j k} (A:Type@{i}) `{SemiDecidable@{i} A}
  (B:Type@{j}) `{SemiDecidable@{j} B}
  : SemiDecidable@{k} (hor@{i j k} A B).
Proof.
split.
- intros E;apply top_le_join in E;revert E;apply (Trunc_ind _);intros [E|E];
  apply semi_decidable in E;apply tr;auto.
- apply (Trunc_ind _);intros [E|E];apply top_le_join,tr;[left|right];
  apply semi_decidable;trivial.
Qed.

Global Instance semi_decide_exists@{i j k} (A : Type@{i}) `{Enumerable@{i} A}
  (B : A -> Type@{j}) `{forall x, SemiDecide@{j} (B x)}
  : SemiDecide@{k} (merely@{k} (exists x, B x))
  := EnumerableSup A (fun x => semi_decide (B x)).
Arguments semi_decide_exists A {_} B {_} /.

Global Instance semi_decidable_exists@{i j k} (A : Type@{i}) `{Enumerable@{i} A}
  (B : A -> Type@{j}) `{!forall x, SemiDecide (B x)}
  `{!forall x, SemiDecidable@{j} (B x)}
  : SemiDecidable (merely@{k} (exists x, B x)).
Proof.
red;unfold semi_decide;simpl.
split.
- intros E;apply top_le_enumerable_sup in E.
  revert E;apply (Trunc_ind _);intros [x E];apply tr;exists x;
  apply semi_decidable,E.
- apply (Trunc_ind _);intros [x E];apply top_le_enumerable_sup,tr;exists x.
  apply (snd semi_decidable),E.
Qed.

Global Instance semi_decide_sier (a : Sier) : SemiDecide a
  := a.
Arguments semi_decide_sier _ /.

Global Instance semi_decidable_sier (a : Sier) : SemiDecidable a.
Proof.
red. split;trivial.
Qed.

Section interleave.

Definition disjoint (a b : Sier) := a -> b -> Empty.

Lemma disjoint_top_l : forall b, disjoint top b -> b = bottom.
Proof.
intros b E. apply bot_eq. apply imply_le.
intros Eb. apply Empty_ind,E;trivial. apply top_greatest.
Qed.

Lemma disjoint_sup_l : forall s b, disjoint (sup _ s) b ->
  forall n, disjoint (s n) b.
Proof.
intros s b E n E1 E2.
apply E;trivial. apply top_le_sup. apply tr;eauto.
Qed.

Lemma disjoint_le_l : forall a b, disjoint a b -> forall a', a' <= a ->
  disjoint a' b.
Proof.
intros a b E a' Ea E1 E2;apply E;trivial. red; transitivity a';trivial.
Qed.

Definition interleave_aux_seq (s : IncreasingSequence Sier)
  (Is : ∀ (n : nat) (b : Sier),
       disjoint (s n) b -> partial bool)
  (Isle : ∀ (n : nat) (b : Sier) (Ea : disjoint (s n) b)
         (Ea' : disjoint (s (S n)) b), (Is n b Ea) ≤ (Is (S n) b Ea'))
  (b : Sier)
  (E : disjoint (sup Unit s) b)
  : IncreasingSequence (partial bool).
Proof.
simple refine (Build_IncreasingSequence _ _).
- intros n. apply (Is n b).
  apply disjoint_sup_l;trivial.
- simpl. auto.
Defined.

Definition interleave_inductors : Inductors Unit
  (fun a => forall b, disjoint a b -> sigT (fun s : partial bool =>
    partial_map (const true) a <= s /\ partial_map (const false) b <= s))
  (fun a a' f g E => forall b Ea Ea', (f b Ea).1 <= (g b Ea').1).
Proof.
simple refine (Build_Inductors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
- intros [] b E. exists (eta _ true).
  split.
  + reflexivity.
  + rewrite (disjoint_top_l _ E). apply bot_least.
- intros b _. exists (partial_map (const false) b).
  split.
  + apply bot_least.
  + reflexivity.
- intros s Is Isle b E.
  simple refine (existT _ _ _);simpl;
  [apply sup;apply (interleave_aux_seq s (fun n b E => (Is n b E).1) Isle b E)|].
  simpl. split.
  + unfold partial_map. rewrite partial_bind_sup_l. apply sup_le_r.
    intros n;simpl.
    change (partial_bind (s n) (eta Bool ∘ const true)) with
      (partial_map (const true) (s n)).
    etransitivity;[|apply (sup_is_ub _ _ n)].
    simpl. auto.
  + etransitivity;[|apply (sup_is_ub _ _ 0)].
    simpl;auto.
- intros a f b Ea Ea'.
  assert (Hrw : Ea = Ea') by apply path_ishprop.
  apply (ap (f b)) in Hrw. apply (ap pr1) in Hrw. rewrite Hrw;reflexivity.
- simpl. intros x f b _ E.
  auto.
- simpl;intros s x Ex fs fs_increasing fb Eb n a Ea Ea'.
  pose proof (fun b Ea Ea' => sup_le_l _ _ _ (Eb b Ea Ea')) as E;
  simpl in E.
  etransitivity;[|simple refine (E _ _ _ n);eapply disjoint_le_l;eauto].
  set (Esup := disjoint_sup_l _ _ _ _).
  assert (Hrw : Ea = Esup) by apply path_ishprop.
  apply (ap (fs n a)),(ap pr1) in Hrw. rewrite <-Hrw;reflexivity.
- simpl. intros s x Ex fs fs_incr fx IHs b ??.
  apply sup_le_r. intros n;simpl.
  auto.
- simpl. intros x y fx fy Ex Ey.
  destruct (partial_antisymm Unit x y Ex Ey);simpl;clear Ex Ey.
  intros Efx Efy.
  apply path_forall;intros b;apply path_forall;intros Eb;
  apply Sigma.path_sigma_hprop.
  apply (antisymmetry le);trivial.
Defined.

Definition interleave : forall a b : Sier, disjoint a b -> partial bool
  := fun a b E => (partial_rect _ _ _ interleave_inductors a b E).1.

Definition interleave_top_l_rw : forall b E, interleave top b E = eta _ true
  := fun _ _ => idpath.

Definition interleave_le : forall a a', a <= a' -> forall b E E',
  interleave a b E <= interleave a' b E'
  := partialLe_rect _ _ _ interleave_inductors.

Definition interleave_sup_l : forall s b E, interleave (sup _ s) b E =
  sup _ (Build_IncreasingSequence
    (fun n => interleave (s n) b (disjoint_sup_l _ _ E _ ))
    (fun n => interleave_le _ _ (seq_increasing _ _) _ _ _))
  := fun _ _ _ => idpath.

Lemma interleave_top_r_rw : forall a E, interleave a top E = eta _ false.
Proof.
apply (partial_ind0 _ (fun a => forall E, _)).
- intros [] E. apply Empty_ind. apply E;apply reflexivity.
- intros E. reflexivity.
- intros s Es E.
  rewrite interleave_sup_l.
  apply (snd (eta_eq_sup_iff bool _ (Build_IncreasingSequence _ _))).
  apply tr;exists 0. simpl.
  apply Es.
Qed.

Lemma interleave_top_l : forall (a b : Sier) E, a ->
  interleave a b E = eta _ true.
Proof.
intros a b E Ea.
apply top_le_eq in Ea.
Symmetry in Ea. destruct Ea. reflexivity.
Qed.

Lemma interleave_top_r : forall(a b : Sier) E, b ->
  interleave a b E = eta _ false.
Proof.
intros a b E Eb.
apply top_le_eq in Eb.
Symmetry in Eb. destruct Eb. apply interleave_top_r_rw.
Qed.

Definition interleave_bot_rw : forall E, interleave bottom bottom E = bot _
  := fun _ => idpath.

Lemma interleave_bot : forall a b E, a <= bottom -> b <= bottom ->
  interleave a b E = bot _.
Proof.
intros a b E E1 E2.
apply bot_eq in E1;apply bot_eq in E2.
Symmetry in E1;Symmetry in E2. destruct E1,E2.
reflexivity.
Qed.

Lemma interleave_le_const_l : forall a b E,
  partial_map (const true) a <= interleave a b E.
Proof.
intros. apply ((partial_rect _ _ _ interleave_inductors a b E).2).
Qed.

Lemma interleave_le_const_r : forall a b E,
  partial_map (const false) b <= interleave a b E.
Proof.
intros. apply ((partial_rect _ _ _ interleave_inductors a b E).2).
Qed.

Lemma interleave_pr : forall a b E v, interleave a b E = eta _ v ->
  match v with true => a | false => b end.
Proof.
apply (partial_ind0 _ (fun a => forall b E v, _ -> _)).
- intros [] b E v Ev.
  apply (injective (eta _)) in Ev.
  rewrite <-Ev;apply top_greatest.
- intros b E v Ev.
  change (partial_map (const false) b = eta _ v) in Ev.
  clear E;revert b v Ev. apply (partial_ind0 _ (fun b => forall v, _ -> _)).
  + intros [] v E. apply (injective (eta _)) in E.
    rewrite <-E;apply top_greatest.
  + intros v E. change (bot _ = eta _ v) in E.
    apply Empty_ind,(not_eta_le_bot bool v). rewrite E;reflexivity.
  + intros s IHs v E.
    unfold partial_map in E;rewrite partial_bind_sup_l in E.
    apply (eta_eq_sup_iff _) in E.
    revert E;apply (Trunc_ind _);intros [n E].
    simpl in E. apply IHs in E.
    destruct v;trivial.
    apply top_le_sup. apply tr;exists n;trivial.
- intros s IHs b E v Ev.
  rewrite interleave_sup_l in Ev.
  apply (eta_eq_sup_iff _) in Ev. simpl in Ev.
  revert Ev;apply (Trunc_ind _);intros [n Ev].
  apply IHs in Ev. destruct v;trivial.
  apply top_le_sup. apply tr;exists n;trivial.
Qed.

End interleave.

End contents.

Arguments semi_decide A {_}.
Arguments decidable_semi_decide _ {_} /.
Arguments semi_decide_conj {_} _ {_} _ {_} /.
Arguments semi_decide_disj {_} _ {_} _ {_} /.
Arguments semi_decide_sier _ /.
Arguments semi_decide_exists {_} A {_} B {_} /.
