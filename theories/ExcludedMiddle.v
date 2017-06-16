Require Import HoTT.Basics HoTT.Types.

(** * The law of excluded middle *)

Monomorphic Axiom ExcludedMiddle : Type0.
Existing Class ExcludedMiddle.

Axiom LEM : forall `{ExcludedMiddle} (P : Type), IsHProp P -> P + ~P.

Definition LEM_type := forall (P : Type), IsHProp P -> P + ~P.

(** ** LEM means that all propositions are decidable *)

Global Instance decidable_lem `{ExcludedMiddle} (P : Type) `{IsHProp P} : Decidable P
  := LEM P _.

(** ** Double-negation elimination *)

Definition DNE := forall P, IsHProp P -> ~~P -> P.

Definition LEM_to_DNE : ExcludedMiddle -> DNE.
Proof.
  intros lem P hp nnp.
  case (LEM P _).
  - auto.
  - intros np; elim (nnp np).
Defined.

(** This direction requires Funext. *)
Definition DNE_to_LEM `{Funext} : 
  DNE -> LEM_type.
Proof.
  intros dn P hp.
  refine (dn (P + ~P) _ _).
  apply ishprop_sum.
  - exact _.
  - exact _.
  - intros p np; exact (np p).
  - intros nlem.
    apply nlem.
    apply inr.
    intros p.
    apply nlem.
    apply inl.
    apply p.
Defined.

(** DNE is equivalent to "every proposition is a negation". *)
Definition allneg_from_DNE (H : DNE) (P : Type) `{IsHProp P}
  : {Q : Type & P <-> ~Q}.
Proof.
  exists (~P); split.
  - intros p np; exact (np p).
  - apply H; exact _.
Defined.

Definition DNE_from_allneg (H : forall P, IsHProp P -> {Q : Type & P <-> ~Q})
  : DNE.
Proof.
  intros P ? nnp.
  destruct (H P _) as [Q e].
  apply e.
  intros q.
  apply nnp.
  intros p.
  exact (fst e p q).
Defined.
