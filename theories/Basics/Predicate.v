Require Import Basics.Overture Basics.Tactics Basics.Iff Basics.Classes.

Set Universe Minimization ToSet.

(** * Predicates on types *)

(** We use the words "subset" and "predicate" interchangably. There is no actual set requirement however. *)

(** ** Predicate equality *)

(** Two predicates are considered "equal" if they are pointwise logically equivalent: [forall x, P x <-> Q x]. We express this with [relation_pointwise] to ease typeclass search. *)
Definition pred_eq {A : Type} := relation_pointwise (fun _ : A => iff).

Instance reflexive_pred_eq {A : Type} : Reflexive (@pred_eq A)
  := _.

Instance symmetric_pred_eq {A : Type} : Symmetric (@pred_eq A)
  := _.

Instance transitive_pred_eq {A : Type} : Transitive (@pred_eq A)
  := _.

(** ** Subsets of a predicate *)

(** [P] is a "subset" of [Q] if [forall x, P x -> Q x]. *)
Definition pred_subset {A : Type} := relation_pointwise (fun (_ : A) (X Y : Type) => X -> Y).

(** TODO: move *)
Instance reflexive_fun : Reflexive (fun A B => A -> B)
  := fun _ => idmap.

(** TODO: move *)
Instance transitive_fun : Transitive (fun A B => A -> B)
  := fun _ _ _ f g => g o f.

(** The subset relation is reflexive. *)
Instance reflexive_pred_subset {A : Type} : Reflexive (@pred_subset A)
  := _.

(** The subset relation is transitive. *)
Instance transitive_pred_subset {A : Type} : Transitive (@pred_subset A)
  := _.

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
  (f : A <~> B)
  : pred_subset (P o f) Q -> pred_subset P (Q o f^-1)
  := pointwise_moveL_equiv _ f P Q.

Definition pred_subset_moveR_equiv {A B : Type} {P : B -> Type} {Q : A -> Type}
  (f : B <~> A)
  : pred_subset P (Q o f) -> pred_subset (P o f^-1) Q
  := pointwise_moveR_equiv _ f P Q.

(** The subset relation is antisymmetric. Note that this isn't [Antisymmetry] as defined in [Basics.Classes] since we get a [pred_eq] rather than a path. Under being a hprop and univalnce, we would get a path. *)
Definition pred_subset_antisymm {A : Type} {P Q : A -> Type}
  : pred_subset P Q -> pred_subset Q P -> pred_eq P Q.
Proof.
  intros p q x; specialize (p x); specialize (q x); by split.
Defined.
