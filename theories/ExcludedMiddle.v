Require Import HoTT.Basics HoTT.Types.

(** * The law of excluded middle *)

Monomorphic Axiom ExcludedMiddle : Type0.
Existing Class ExcludedMiddle.

Axiom LEM : forall `{ExcludedMiddle} (P : Type), IsHProp P -> P + ~P.

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
  DNE -> forall (P : Type), IsHProp P -> P + ~P.
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
