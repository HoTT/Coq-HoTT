Require Import Basics.Overture Basics.Tactics Basics.Iff Basics.Classes.

Set Universe Minimization ToSet.

(** * Predicates on types *)

(** We use the words "subset" and "predicate" interchangably to mean something of type [A -> Type]. *)

(** ** Predicate equality *)

(** Two predicates are considered "equal" if they are pointwise logically equivalent: [forall a, P a <-> Q a]. We express this with [relation_pointwise] to ease typeclass search. *)
Definition pred_eq {A : Type} := relation_pointwise (fun _ : A => iff).

(** It follows from [reflexive_pointwise], [transitive_pointwise] and [symmetric_pointwise] that [pred_eq] is reflexive, transitive and symmetric. *)

(** ** Subsets of a predicate *)

(** A predicate [P] is a "subset" of a predicate [Q] if [forall a, P a -> Q a]. *)
Definition pred_subset {A : Type} := relation_pointwise (fun (_ : A) => (->)).

(** It follows from [reflexive_pointwise] and [transitive_pointwise] that [pred_subset] is reflexive and transitive. *)

Coercion pred_eq_subset {A : Type} (P Q : A -> Type)
  : pred_eq P Q -> pred_subset P Q
  := fun p x => fst (p x).

Definition pred_eq_subset' {A : Type} (P Q : A -> Type)
  : pred_eq P Q -> pred_subset Q P
  := fun p x => snd (p x).

Definition pred_subset_precomp {A B : Type} {P Q : B -> Type} (f : A -> B)
  : pred_subset P Q -> pred_subset (P o f) (Q o f)
  := pointwise_precomp _ f P Q.

Definition pred_subset_moveL_equiv {A B : Type} {P : B -> Type} {Q : A -> Type}
  (f : B <~> A)
  : pred_subset (P o f^-1) Q -> pred_subset P (Q o f)
  := pointwise_moveL_equiv _ f P Q.

Definition pred_subset_moveR_equiv {A B : Type} {P : B -> Type} {Q : A -> Type}
  (f : A <~> B)
  : pred_subset P (Q o f^-1) -> pred_subset (P o f) Q
  := pointwise_moveR_equiv _ f P Q.

(** The subset relation is antisymmetric. Note that this isn't [Antisymmetry] as defined in [Basics.Classes] since we get a [pred_eq] rather than a path. Under being a hprop and univalance, we would get a path. *)
Definition pred_subset_antisymm {A : Type} {P Q : A -> Type}
  : pred_subset P Q -> pred_subset Q P -> pred_eq P Q.
Proof.
  intros p q x; specialize (p x); specialize (q x); by split.
Defined.
