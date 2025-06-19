Require Import Basics.Overture Basics.Tactics Basics.Iff Basics.Classes Basics.Utf8.

Set Universe Minimization ToSet.

(** * Predicates on types *)

(** We use the words "predicate" and "(type) family" interchangably to mean something of type [A -> Type]. *)

(** ** Predicate equality *)

(** Two predicates are considered "equal" if they are pointwise logically equivalent: [forall a, P a <-> Q a]. We express this with [relation_pointwise] to ease typeclass search. *)
Definition pred_eq {A : Type} := relation_pointwise (fun _ : A => iff).

(** It follows from [reflexive_pointwise], [transitive_pointwise] and [symmetric_pointwise] that [pred_eq] is reflexive, transitive and symmetric. *)

(** ** Subsets of a predicate *)

(** A predicate [P] is a "subset" of a predicate [Q] if [forall a, P a -> Q a]. *)
Definition pred_subset {A : Type} := relation_pointwise (fun (_ : A) => (->)).

(** *** Predicate Notations *)

Declare Scope predicate_scope.
Local Open Scope predicate_scope.

Infix "⊆" := pred_subset : predicate_scope.
Infix "↔" := pred_eq     : predicate_scope.

(** *** Properties of subsets *)

(** It follows from [reflexive_pointwise] and [transitive_pointwise] that [pred_subset] is reflexive and transitive. *)

Coercion pred_subset_pred_eq {A : Type} (P Q : A -> Type)
  : P ↔ Q -> P ⊆ Q
  := fun p x => fst (p x).

Definition pred_subset_pred_eq' {A : Type} (P Q : A -> Type)
  : P ↔ Q -> Q ⊆ P
  := fun p x => snd (p x).

(** The subset relation is antisymmetric. Note that this isn't [Antisymmetry] as defined in [Basics.Classes] since we get a [pred_eq] rather than a path. Under being a hprop and univalance, we would get a path. *)
Definition pred_subset_antisymm {A : Type} {P Q : A -> Type}
  : P ⊆ Q -> Q ⊆ P -> P ↔ Q.
Proof.
  intros p q x; specialize (p x); specialize (q x); by split.
Defined.

Definition pred_subset_precomp {A B : Type} {P Q : B -> Type} (f : A -> B)
  : P ⊆ Q -> (P o f) ⊆ (Q o f)
  := pointwise_precomp _ f P Q.

Definition pred_subset_postcomp {A : Type} {P Q : A -> Type}
  (F : Type -> Type) (f : forall {X Y}, (X -> Y) -> F X -> F Y) (p : P ⊆ Q)
  : (F o P) ⊆ (F o Q)
  := fun x => f (p x).

Definition pred_subset_moveL_equiv {A B : Type} {P : B -> Type} {Q : A -> Type}
  (f : B <~> A)
  : (P o f^-1) ⊆ Q -> P ⊆ (Q o f)
  := pointwise_moveL_equiv _ f P Q.

Definition pred_subset_moveR_equiv {A B : Type} {P : B -> Type} {Q : A -> Type}
  (f : A <~> B)
  : P ⊆ (Q o f^-1) -> (P o f) ⊆ Q
  := pointwise_moveR_equiv _ f P Q.

Section OperationsAndIdentities.

(** ** Operations on predicates *)

  Context {A : Type}.
  Local Notation Pred := (A -> Type).

  Definition pred_and (P Q : Pred) : Pred
    := fun a => P a /\ Q a.

  Definition pred_or (P Q : Pred) : Pred
    := fun a => P a + Q a.

  (** ** True and false predicates *)

  Definition pred_unit : Pred
    := fun _ => Unit.

  Definition pred_empty : Pred
    := fun _ => Empty.

  (** ** Relationships between predicates *)

  Definition pred_empty_subset (P : Pred) : pred_empty ⊆ P
    := fun _ => Empty_rec _.

  Definition pred_unit_subset (P : Pred) : P ⊆ pred_unit
    := fun _ _ => tt.

  Definition pred_and_subset_l (P Q : Pred) : pred_and P Q ⊆ P
    := fun _ => fst.

  Definition pred_and_subset_r (P Q : Pred) : pred_and P Q ⊆ Q
    := fun _ => snd.

  Definition pred_and_is_meet (P Q R : Pred) (p : R ⊆ P) (q : R ⊆ Q)
    : R ⊆ pred_and P Q
    := fun a r => ((p a r), (q a r)).

  Definition pred_and_comm' (P Q : Pred)
    : pred_and P Q ⊆ pred_and Q P
    := fun a pq => (snd pq, fst pq).

  Definition pred_and_comm (P Q : Pred)
    : pred_and P Q ↔ pred_and Q P
    := pred_subset_antisymm (pred_and_comm' P Q) (pred_and_comm' Q P).

  Definition pred_or_is_join (P Q R : Pred) (p : P ⊆ R) (q : Q ⊆ R)
    : pred_or P Q ⊆ R
    := fun a pq => match pq with
                 | inl l => p a l
                 | inr r => q a r end.

  Definition pred_or_comm' (P Q : Pred)
    : pred_or P Q ⊆ pred_or Q P
    := fun a pq => match pq with
                 | inl p => inr p
                 | inr q => inl q end.

  Definition pred_or_comm (P Q : Pred)
    : pred_or P Q ↔ pred_or Q P
    := pred_subset_antisymm (pred_or_comm' P Q) (pred_or_comm' Q P).

  Definition pred_and_unit_l (P : Pred) : pred_and pred_unit P ↔ P.
  Proof.
    apply pred_subset_antisymm.
    1: apply pred_and_subset_r.
    apply pred_and_is_meet.
    - apply pred_unit_subset.
    - reflexivity.
  Defined.

  Definition pred_and_unit_r (P : Pred) : pred_and P pred_unit ↔ P.
  Proof.
    apply pred_subset_antisymm.
    1: apply pred_and_subset_l.
    apply pred_and_is_meet.
    - reflexivity.
    - apply pred_unit_subset.
  Defined.

End OperationsAndIdentities.
