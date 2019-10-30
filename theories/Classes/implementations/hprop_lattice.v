Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.HProp HoTT.TruncType
  HoTT.Types.Universe HoTT.Types.Prod.

(** Demonstrate the [hProp] is a (bounded) lattice w.r.t. the logical
operations. This requires Univalence. *)
Instance join_hor : Join hProp := hor.
Definition hand (X Y : hProp) : hProp := BuildhProp (X * Y).
Instance meet_hprop : Meet hProp := hand.
Instance bottom_hprop : Bottom hProp := False_hp.
Instance top_hprop : Top hProp := Unit_hp.

Section contents.
  Context `{Univalence}.

  (* We use this notation because [hor] can accept arguments of type [Type], which leads to minor confusion in the instances below *)
  Notation lor := (hor : hProp -> hProp -> hProp).

  (* This tactic attempts to destruct a truncated sum (disjunction) *)
  Local Ltac hor_intros :=
    let x := fresh in
    intro x; repeat (strip_truncations; destruct x as [x | x]).

  Instance commutative_hor : Commutative lor.
  Proof.
    intros ??.
    apply path_iff_hprop; hor_intros; apply tr; auto.
  Defined.

  Instance commutative_hand : Commutative hand.
  Proof.
    intros ??.
    apply path_hprop.
    apply equiv_prod_symm.
  Defined.

  Instance associative_hor : Associative lor.
  Proof.
    intros ???.
    apply path_iff_hprop;
    hor_intros; apply tr;
    ((by auto) || (left; apply tr) || (right; apply tr));
    auto.
  Defined.

  Instance associative_hand : Associative hand.
  Proof.
    intros ???.
    apply path_hprop.
    apply equiv_prod_assoc.
  Defined.

  Instance idempotent_hor : BinaryIdempotent lor.
  Proof.
    intros ?. compute.
    apply path_iff_hprop; hor_intros; auto.
    by apply tr, inl.
  Defined.

  Instance idempotent_hand : BinaryIdempotent hand.
  Proof.
    intros ?.
    apply path_iff_hprop.
    - intros [a _] ; apply a.
    - intros a; apply (pair a a).
  Defined.

  Instance leftidentity_hor : LeftIdentity lor False_hp.
  Proof.
    intros ?.
    apply path_iff_hprop; hor_intros; try contradiction || assumption.
    by apply tr, inr.
  Defined.

  Instance rightidentity_hor : RightIdentity lor False_hp.
  Proof.
    intros ?.
    apply path_iff_hprop; hor_intros; try contradiction || assumption.
    by apply tr, inl.
  Defined.

  Instance leftidentity_hand : LeftIdentity hand Unit_hp.
  Proof.
    intros ?.
    apply path_trunctype, prod_unit_l.
  Defined.

  Instance rightidentity_hand : RightIdentity hand Unit_hp.
  Proof.
    intros ?.
    apply path_trunctype, prod_unit_r.
  Defined.

  Instance absorption_hor_hand : Absorption lor hand.
  Proof.
    intros ??.
    apply path_iff_hprop.
    - intros X; strip_truncations.
      destruct X as [? | [? _]]; assumption.
    - intros ?. by apply tr, inl.
  Defined.

  Instance absorption_hand_hor : Absorption hand lor.
  Proof.
    intros ??.
    apply path_iff_hprop.
    - intros [? _]; assumption.
    - intros ?.
      split.
      * assumption.
      * by apply tr, inl.
  Defined.

  Global Instance boundedlattice_hprop : IsBoundedLattice hProp.
  Proof. repeat split; apply _. Defined.
End contents.
