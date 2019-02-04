Require Import HoTT.Basics HoTT.Types.

(** * The law of excluded middle *)

Monomorphic Axiom ExcludedMiddle : Type0.
Existing Class ExcludedMiddle.

Axiom LEM : forall `{ExcludedMiddle} (P : Type), IsHProp P -> P + ~P.

Definition ExcludedMiddle_type := forall (P : Type), IsHProp P -> P + ~P.

(** ** LEM means that all propositions are decidable *)

Global Instance decidable_lem `{ExcludedMiddle} (P : Type) `{IsHProp P} : Decidable P
  := LEM P _.

(** ** Double-negation elimination *)

Definition DNE_type := forall P, IsHProp P -> ~~P -> P.

Definition LEM_to_DNE : ExcludedMiddle -> DNE_type.
Proof.
  intros lem P hp nnp.
  case (LEM P _).
  - auto.
  - intros np; elim (nnp np).
Defined.

(** This direction requires Funext. *)
Definition DNE_to_LEM `{Funext} : 
  DNE_type -> ExcludedMiddle_type.
Proof.
  intros dn P hp.
  refine (dn (P + ~P) _ _).
  - apply ishprop_sum.
    + exact _.
    + exact _.
    + intros p np; exact (np p).
  - intros nlem.
    apply nlem.
    apply inr.
    intros p.
    apply nlem.
    apply inl.
    apply p.
Defined.

(** DNE is equivalent to "every proposition is a negation". *)
Definition allneg_from_DNE (H : DNE_type) (P : Type) `{IsHProp P}
  : {Q : Type & P <-> ~Q}.
Proof.
  exists (~P); split.
  - intros p np; exact (np p).
  - apply H; exact _.
Defined.

Definition DNE_from_allneg (H : forall P, IsHProp P -> {Q : Type & P <-> ~Q})
  : DNE_type.
Proof.
  intros P ? nnp.
  destruct (H P _) as [Q e].
  apply e.
  intros q.
  apply nnp.
  intros p.
  exact (fst e p q).
Defined.
