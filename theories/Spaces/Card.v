(* -*- mode: coq; mode: visual-line -*- *)
(** Representation of cardinals, see Chapter 10 of the HoTT book. *)
Require Import Basics.
Require Import HSet.
Require Import TruncType.
Require Import Types.
Require Import Classes.interfaces.abstract_algebra.
Require Import HIT.Truncations.
Require Import Spaces.Finite.
Require Import Types.Sigma.
Require Import ExcludedMiddle.

(** ** Definitions and operations *)

Definition Card := Trunc 0 hSet.

Definition sum_card (a b : Card) : Card.
Proof.
  strip_truncations.
  refine (tr (BuildhSet (a + b))).
Defined.

Definition prod_card (a b : Card) : Card.
Proof.
  strip_truncations.
  refine (tr (BuildhSet (a * b))).
Defined.

Definition exp_card `{Funext} (b a : Card) : Card.
Proof.
  strip_truncations.
  refine (tr (BuildhSet (b -> a))).
Defined.

Definition leq_card `{Univalence} : Card -> Card -> hProp.
Proof.
  refine (Trunc_rec (fun a => _)).
  refine (Trunc_rec (fun b => _)).
  refine (hexists (fun (i : a -> b) => isinj i)).
Defined.

Definition lt_card `{Univalence} (a : Card) (b : Card) : hProp :=
  BuildhProp ((leq_card a b) * (a <> b)).

(** Cardinals **)

Section Cardinals.
  Definition zero : Card := tr (BuildhSet Empty).
  Definition one  : Card := tr (BuildhSet Unit).
  Definition two  : Card := tr (BuildhSet Bool).

  Definition nat_card (n : nat) : Card := tr (BuildhSet (Fin n)).

  Definition aleph_0 : Card := tr (BuildhSet nat).

  (** TODO: 
    Perhaps include "sucessor" cardinals aleph_n upto some assumptions.

    This would allow us to define aleph_w as the infinite union over N

    This is a nice cardinal to have because it's an example of one that isn't
    regular.
  **)


End Cardinals.


(** ** Properties *)
Section contents.
  Context `{Univalence}.

  Global Instance plus_card : Plus Card := sum_card.
  Global Instance mult_card : Mult Card := prod_card.
  Global Instance zero_card : Zero Card := zero.
  Global Instance one_card  : One Card  := one.
  Global Instance le_card   : Le Card   := leq_card.

  (* Reduce an algebraic equation to an equivalence *)
  Local Ltac reduce :=
    repeat (intros ?); strip_truncations; cbn; f_ap; apply path_hset.

  (* Simplify an equation by unfolding all the definitions apart from
  the actual operations. *)
  Local Ltac simpl_ops :=
    cbv-[plus_card mult_card zero_card one_card].

  (** We only make the instances of upper classes global, since the
  other instances will be project anyway. *)

  (** *** [Card] is a semi-ring *)
  Instance associative_sum : Associative plus_card.
  Proof. reduce. symmetry. apply equiv_sum_assoc. Defined.

  Instance rightid_sum : RightIdentity plus_card zero_card.
  Proof. reduce. apply sum_empty_r. Defined.

  Instance commutative_sum : Commutative plus_card.
  Proof. reduce. apply equiv_sum_symm. Defined.

  Instance associative_prod : Associative mult_card.
  Proof. reduce. apply equiv_prod_assoc. Defined.

  Instance rightid_prod : RightIdentity mult_card one_card.
  Proof. reduce. apply prod_unit_r. Defined.

  Instance commutative_prod : Commutative mult_card.
  Proof. reduce. apply equiv_prod_symm. Defined.

  Instance leftdistributive_card : LeftDistribute mult_card plus_card.
  Proof. reduce. apply sum_distrib_l. Defined.

  Instance leftabsorb_card : LeftAbsorb mult_card zero_card.
  Proof. reduce. apply prod_empty_l. Defined.

  Global Instance semiring_card : SemiRing Card.
  Proof.
    repeat split; try apply _.
    - repeat intro. simpl_ops.
      rewrite (commutativity zero_card _).
      apply rightid_sum.
    - repeat intro. simpl_ops.
      rewrite (commutativity one_card _).
      apply rightid_prod.
  Defined.

  (** *** Properties of exponentiation *)
  Lemma exp_zero_card (a : Card) : exp_card 0 a = 1.
  Proof. simpl_ops. reduce. symmetry. apply equiv_empty_rec. Defined.

  Lemma exp_card_one (a : Card) : exp_card a 1 = 1.
  Proof. simpl_ops. reduce. symmetry. apply equiv_unit_coind. Defined.

  Lemma exp_one_card (a : Card) : exp_card 1 a = a.
  Proof. reduce. symmetry. apply equiv_unit_rec. Defined.

  Lemma exp_card_sum_mult (a b c : Card) :
    exp_card (b + c) a = (exp_card b a) * (exp_card c a).
  Proof. reduce. symmetry. apply equiv_sum_distributive. Defined.

  Lemma exp_mult_card_exp (a b c : Card) :
    exp_card (b * c) a = exp_card c (exp_card b a).
  Proof.
    rewrite (@commutativity _ _ (.*.) _ b c).
    reduce. symmetry. apply equiv_uncurry.
  Defined.

  Lemma exp_card_mult_mult (a b c : Card) :
    exp_card c (a * b) = (exp_card c a) * (exp_card c b).
  Proof. reduce. symmetry. apply equiv_prod_coind. Defined.

  (* Cantor's theorem *)
  Lemma card_ne_exp_two_card (a : Card) :
    a <> (exp_card a two).
  Proof.
    unfold Card in *; strip_truncations; cbn.
    intros e.
    apply ((equiv_path_Tr (A := hSet) a (BuildhSet (a -> Bool)))^-1) in e.
    strip_truncations.
    apply ((equiv_path_trunctype a (BuildhSet (a -> Bool)))^-1) in e.
    destruct a as [A ?]. cbn in e.
    pose (f := (fun a:A => negb (e a a))).
    pose (a0 := e^-1 f).
    pose (b := f a0).
    assert (bb : negb (e (e^-1 f) a0) = b) by reflexivity.
    rewrite eisretr in bb. fold b in bb.
    exact (not_fixed_negb b bb).
  Defined.

  Lemma card_lt_exp_two_card `{ExcludedMiddle} (a : Card) :
    lt_card a (exp_card a two).
  Proof.
    strip_truncations; split; simpl.
    + serapply (tr ( _ ; _ )).
      - intros x y.
        destruct (LEM (x = y) _).
        * refine true.
        * refine false.
      - intros x y e.
        apply ap10 in e; specialize (e x); cbn in e.
        destruct (LEM (x = x) _) as [?|q1], (LEM (y = x) _).
        * symmetry; assumption.
        * elim (true_ne_false e).
        * elim (false_ne_true e).
        * elim (q1 idpath).
    + apply card_ne_exp_two_card.
  Defined.

  (** *** Properties of ≤ *)
  Instance reflexive_card : Reflexive leq_card.
  Proof.
    intro x. strip_truncations.
    apply tr. exists idmap. refine (fun _ _ => idmap).
  Defined.

  Instance transitive_card : Transitive leq_card.
  Proof.
    intros a b c. strip_truncations.
    intros Hab Hbc. strip_truncations.
    destruct Hab as [iab Hab].
    destruct Hbc as [ibc Hbc].
    apply tr. exists (ibc ∘ iab).
    intros x y Hxy.
    apply Hab. apply Hbc. apply Hxy.
  Defined.

  Global Instance preorder_card : PreOrder le_card.
  Proof. split; apply _. Defined.

  (* If we can give two elements of a set we can assure it has a 
     cardinality less than or equal to the cardinaity of Bool.

     Another way of phrasing this is if there exists an injection
     i : Bool -> X, this can be generalised to any finite set. *)
  Lemma bool_leq_at_least_two {X : hSet} (x y : X) `{x <> y} 
    : leq_card two (tr X).
  Proof.
    simpl; apply tr; srefine (_;_).
    refine (fun b => if b then x else y).
    simpl; unfold isinj; intros a b p.
      destruct a, b.
      reflexivity.
      apply H0 in p; elim p.
      apply symmetry in p; apply H0 in p; elim p.
      reflexivity.
  Defined.


  Section Regular.

    (** Definition of regular cardinals (from nlab)

    An infinite cardinal κ\kappa is a regular cardinal if it 
    satisfies the following equivalent properties:

     1. no set (in a material set theory) of cardinality κ\kappa 
      is the union of fewer than κ\kappa sets of cardinality 
      less than κ\kappa.

     2. no set (in a structural set theory) of cardinality κ\kappa 
      is the disjoint union of fewer than κ\kappa sets of 
      cardinality less than κ\kappa.

     3. given a function P→XP \to X (regarded as a family 
      of sets {P x} x∈X\{P_x\}_{x\in X}) such that 
      |X|<κ{|X|} \lt \kappa and |P x|<κ{|P_x|} \lt \kappa for 
      all x∈Xx \in X, then |P|<κ{|P|} \lt \kappa.

     4. the category Set <κ\Set_{\lt\kappa} of sets of 
      cardinality <κ\lt\kappa has all colimits 
      (or just all coproducts) of size <κ\lt\kappa.

     5. the cofinality of κ\kappa is equal to κ\kappa.

    A cardinal that is not regular is called singular.


    We are not working in a material set theory so we can't choose 1.
    Definitions 2, 3, 4 seem the most likely. I (Ali) am not familar
    with 5 and 4 relies on categorical machinary which I see no reason
    to have to use.

    Definition 3 essentially says for every X, for every family 
    of sets P : X -> Set_U such that X and the fibers of P have 
    cardinality less than k, then the total space (set) has cardinality
    less then k. I don't know if this is an easy thing to prove in practice
    but seems like the kind of thing HoTT is good at.

    Definition 2 would require defining disjoint unions. And I am sure
    it is basically the same thing as 3.

**)

  Notation "| X | < k" := (lt_card (tr X) k) (at level 20) : card_scope.
  Notation "| X | < k" := (lt_card (tr (BuildhSet X)) k) (at level 20) : card_scope.

  Context {X : hSet}.
  Context {P : X -> hSet}.

  Local Open Scope card_scope.

  Definition regular (k : Card) `{|X| <  k} `{forall x, |P x| < k} :=
        |exists (x:X), P x| < k.

  End Regular.
End contents.
