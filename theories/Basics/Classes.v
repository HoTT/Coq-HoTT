Require Import Basics.Overture Basics.Tactics.

(** * Classes *)

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

Global Instance isinj_idmap A : @IsInjective A A idmap
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
