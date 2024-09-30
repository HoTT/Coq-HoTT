(** * Impredicative truncations *)

(** In this file, under the assumptions of propositional resizing [PropResizing] and function extensionality [Funext], we define the proposition truncation in any universe except the bottom universe.  We use primes when necessary to distinguish these from the constructions made using HITs. *)

Require Import HoTT.Basics.
Require Import Universes.Smallness.
Local Open Scope path_scope.

(** Using only function extensionality, we can define a "propositional truncation" [merely' A] of a type [A] in universe [i].  However, if we want it to land in the same universe [i], then we must restrict ourselves to quantifying over propositions [P] in a strictly smaller universe [j]. *)
Definition merely'@{i j | j < i} (A : Type@{i}) : Type@{i}
  := forall P:Type@{j}, IsHProp P -> (A -> P) -> P.

Definition trm@{i j | j < i} {A : Type@{i}} : A -> merely'@{i j} A
  := fun a P HP f => f a.

Global Instance ishprop_merely@{i j | j < i} `{Funext} (A : Type@{i})
  : IsHProp (merely'@{i j} A)
  := _.

(** Because of this, it will only eliminate into propositions in that smaller universe [j]. *)
Definition merely_rec_naive@{i j | j < i} {A : Type@{i}}
  {P : Type@{j}} {p : IsHProp@{j} P} (f : A -> P)
  : merely'@{i j} A -> P
  := fun ma => ma P p f.

(** And then the functoriality will also impose a universe constraint [i' <= j < i]. *)
Definition functor_merely_naive@{i j i' j' | j < i, j' < i', i' <= j} `{Funext}
  {A : Type@{i}} {A' : Type@{i'}} (f : A -> A')
  : merely'@{i j} A -> merely'@{i' j'} A'
  := merely_rec_naive (trm o f).

(** These problems go away if we assume propositional resizing. *)

Section AssumePropResizing.
  Context `{PropResizing}.

  (** Here we use propositional resizing to resize a arbitrary proposition [P] from an arbitrary universe [k] to universe [j], so there is no constraint on the universe [k].  In particular, we can take [k = i], which shows that [merely'] is a reflective subuniverse of [Type@{i}], since any two maps into a proposition agree. *)
  Definition merely_rec'@{i j k | j < i} {A : Type@{i}}
    {P : Type@{k}} `{IsHProp P} (f : A -> P)
    : merely'@{i j} A -> P
    := fun ma => (equiv_smalltype@{j k} P)
                 (ma (smalltype@{j k} P) _ ((equiv_smalltype@{j k} P)^-1 o f)).

  (** Similarly, there are no constraints between [i] and [i'] in the next definition, so they could be taken to be equal. *)
  Definition functor_merely@{i j i' j' | j < i, j' < i'} `{Funext} {A : Type@{i}} {A' : Type@{i'}} (f : A -> A')
    : merely'@{i j} A -> merely'@{i' j'} A'
    := merely_rec' (trm o f).

End AssumePropResizing.
