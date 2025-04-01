Require Import Basics.Overture Basics.Tactics.

(** * Classes *)

(** ** Pointwise Lemmas *)

Section Pointwise.

  Context {A : Type} {B : A -> Type} (R : forall a, Relation (B a)).

  Definition relation_pointwise : Relation (forall x, B x)
    := fun P Q => forall x, R x (P x) (Q x).

  Definition reflexive_pointwise `{!forall a, Reflexive (R a)}
    : Reflexive relation_pointwise.
  Proof.
    intros P x; reflexivity.
  Defined.

  Definition transitive_pointwise `{!forall a, Transitive (R a)}
    : Transitive relation_pointwise.
  Proof.
    intros P Q S x y a.
    by transitivity (Q a).
  Defined.

  Definition symmetric_pointwise `{!forall a, Symmetric (R a)}
    : Symmetric relation_pointwise.
  Proof.
    intros P Q x a.
    by symmetry.
  Defined.

End Pointwise.

Hint Immediate reflexive_pointwise : typeclass_instances.
Hint Immediate transitive_pointwise : typeclass_instances.
Hint Immediate symmetric_pointwise : typeclass_instances.

(** ** Injective Functions *)

Class IsInjective {A B : Type} (f : A -> B)
  := injective : forall x y, f x = f y -> x = y.
Arguments injective {A B} f {_} _ _.

Definition neq_isinj {A B : Type} (f : A -> B) `{!IsInjective f}
  : forall x y, x <> y -> f x <> f y.
Proof.
  intros x y np q.
  apply np, (injective f).
  exact q.
Defined.

Instance isinj_idmap A : @IsInjective A A idmap
  := fun x y => idmap.

#[export] Hint Unfold IsInjective : typeclass_instances.

Definition isinj_compose {A B C f g} `{IsInjective B C g} `{IsInjective A B f}
  : IsInjective (g o f).
Proof.
  intros x y p.
  by apply (injective f), (injective g).
Defined.
#[export] Hint Immediate isinj_compose : typeclass_instances.

Definition isinj_cancelL {A B C : Type} (f : A -> B) (g : B -> C)
  `{!IsInjective (g o f)}
  : IsInjective f.
Proof.
  intros x y p.
  apply (injective (g o f)).
  exact (ap g p).
Defined.

(** ** Antisymmetric Relations *)

Class AntiSymmetric {A : Type} (R : A -> A -> Type) : Type
  := antisymmetry : forall x y, R x y -> R y x -> x = y.
Arguments antisymmetry {A} R {AntiSymmetric} x y _ _.
