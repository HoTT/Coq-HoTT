Require Import Basics.Overture Basics.Tactics Basics.Iff Basics.Classes.

Set Universe Minimization ToSet.

(** * Predicates on types *)

(** We use the words "subset" and "predicate" interchangably. There is no actual set requirement however. *)

(** ** Predicate equality *)

Definition pred_eq {A : Type} (P Q : A -> Type) := forall x, P x <-> Q x.

Instance reflexive_pred_eq {A : Type} : Reflexive (@pred_eq A)
  := reflexive_pointwise (fun _ => _).

Instance symmetric_pred_eq {A : Type} : Symmetric (@pred_eq A)
  := symmetric_pointwise (fun _ => _).

Instance transitive_pred_eq {A : Type} : Transitive (@pred_eq A)
  := transitive_pointwise (fun _ => _).

(** ** Subsets of a predicate *)

Definition pred_subset {A : Type} (P Q : A -> Type) := (forall x, P x -> Q x).

(** TODO: move *)
Instance reflexive_fun : Reflexive (fun A B => A -> B)
  := fun _ => idmap.

(** TODO: move *)
Instance transitive_fun : Transitive (fun A B => A -> B)
  := fun _ _ _ f g => g o f.

(** The subset relation is reflexive. *)
Instance reflexive_pred_subset {A : Type} : Reflexive (@pred_subset A)
  := reflexive_pointwise (B:=fun x => Type) (fun _ A B => A -> B).

(** The subset relation is transitive. *)
Instance transitive_pred_subset {A : Type} : Transitive (@pred_subset A)
 := transitive_pointwise (B:=fun x => Type) (fun _ A B => A -> B).

Coercion pred_eq_subset {A : Type} (P Q : A -> Type)
  : pred_eq P Q -> pred_subset P Q
  := fun p x => fst (p x).

(** The subset relation is antisymmetric. Note that this isn't [Antisymmetry] as defined in [Basics.Classes] since we get a [pred_eq] rather than a path. Under being a hprop and univalnce, we would get a path. *)
Definition pred_subset_antisymm {A : Type} {P Q : A -> Type}
  : pred_subset P Q -> pred_subset Q P -> pred_eq P Q.
Proof.
  intros p q x; specialize (p x); specialize (q x); by split.
Defined.
