(** Representation of cardinals, see Chapter 10 of the HoTT book. *)
Require Import HoTT.Universes.TruncType.
Require Import HoTT.Classes.interfaces.abstract_algebra.

(** This speeds things up considerably *)
Local Opaque equiv_isequiv istrunc_isequiv_istrunc.

(** ** Definitions and operations *)

Definition Card := Trunc 0 HSet.

Definition card A `{IsHSet A} : Card
  := tr (Build_HSet A).

Definition sum_card (a b : Card) : Card.
Proof.
  strip_truncations.
  refine (tr (Build_HSet (a + b))).
Defined.

Definition prod_card (a b : Card) : Card.
Proof.
  strip_truncations.
  refine (tr (Build_HSet (a * b))).
Defined.

Definition exp_card `{Funext} (b a : Card) : Card.
Proof.
  strip_truncations.
  refine (tr (Build_HSet (b -> a))).
Defined.

Definition leq_card `{Univalence} : Card -> Card -> HProp.
Proof.
  refine (Trunc_rec (fun a => _)).
  refine (Trunc_rec (fun b => _)).
  exact (hexists (fun (i : a -> b) => IsInjective i)).
Defined.

(** ** Properties *)
Section contents.
  Context `{Univalence}.

  Global Instance plus_card : Plus Card := sum_card.
  Global Instance mult_card : Mult Card := prod_card.
  Global Instance zero_card : Zero Card := tr (Build_HSet Empty).
  Global Instance one_card : One Card := tr (Build_HSet Unit).
  Global Instance le_card : Le Card := leq_card.

  (* Reduce an algebraic equation to an equivalence *)
  Local Ltac reduce :=
    repeat (intros ?); strip_truncations; cbn; f_ap; apply path_hset.

  (* Simplify an equation by unfolding all the definitions apart from
  the actual operations. *)
  (* Note that this is an expensive thing to do, and will be very slow unless we tell it not to unfold the following. *)
  Local Ltac simpl_ops :=
    cbv-[plus_card mult_card zero_card one_card exp_card].

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

  Global Instance issemiring_card : IsSemiCRing Card.
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

End contents.


(** * Cardinality comparisons *)

(* We also work with cardinality comparisons directly to avoid unnecessary type truncations via cardinals. *)

Definition Injection X Y :=
  { f : X -> Y | IsInjective f }.

Global Instance Injection_refl :
  Reflexive Injection.
Proof.
  intros X. exists (fun x => x). intros x x'. done.
Qed.

Lemma Injection_trans X Y Z :
  Injection X Y -> Injection Y Z -> Injection X Z.
Proof.
  intros [f Hf] [g Hg]. exists (fun x => g (f x)).
  intros x x' H. by apply Hf, Hg.
Qed.

Definition InjectsInto X Y :=
  merely (Injection X Y).

Global Instance InjectsInto_refl :
  Reflexive InjectsInto.
Proof.
  intros X. apply tr. reflexivity.
Qed.

Lemma InjectsInto_trans X Y Z :
  InjectsInto X Y -> InjectsInto Y Z -> InjectsInto X Z.
Proof.
  intros H1 H2.
  eapply merely_destruct; try apply H1. intros [f Hf].
  eapply merely_destruct; try apply H2. intros [g Hg].
  apply tr. exists (fun x => g (f x)).
  intros x x' H. by apply Hf, Hg.
Qed.



(** * Infinity *)

(* We call a set infinite if nat embeds into it. *)

Definition infinite X :=
  Injection nat X.
