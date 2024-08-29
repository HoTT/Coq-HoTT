Require Import Basics.Overture Basics.Tactics.

Local Set Universe Minimization ToSet.

(** * If and only if *)

(** ** Definition *)

(** [iff A B], written [A <-> B], expresses the logical equivalence of [A] and [B] *)
Definition iff (A B : Type) := prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

(** ** Basic Properties *)

(** Everything is logically equivlaent to itself. *)
Definition iff_refl {A} : A <-> A
  := (idmap , idmap).

(** [iff] is a reflexive relation. *)
Global Instance iff_reflexive : Reflexive iff | 1
  := @iff_refl.

(** Logical equivalences can be inverted. *)
Definition iff_inverse {A B} : (A <-> B) -> (B <-> A)
  :=  fun f => (snd f , fst f).

(** [iff] is a symmetric relation. *)
Global Instance symmetric_iff : Symmetric iff | 1
  := @iff_inverse.

(** Logical equivalences can be composed. *)
Definition iff_compose {A B C} (f : A <-> B) (g : B <-> C) : A <-> C
  := (fst g o fst f , snd f o snd g).

(** [iff] is a transitive relation. *)
Global Instance transitive_iff : Transitive iff | 1
  := @iff_compose.

(** Any equivalence can be considered a logical equivalence by discarding everything but the maps. We make this a coercion so that equivalences can be used in place of logical equivalences. *)
Coercion iff_equiv {A B : Type} (f : A <~> B)
  : A <-> B := (equiv_fun f, f^-1).

(** ** Logical Laws *)

(** One of De Morgan's Laws.  The dual statement about negating a product appears in Decidable.v due to decidability requirements. *)
Definition iff_not_sum A B : ~ (A + B) <-> ~ A * ~ B.
Proof.
  split.
  - intros ns.
    exact (ns o inl, ns o inr).
  - by intros []; snrapply sum_ind.
Defined.

Definition iff_contradiction A : A * ~A <-> Empty.
Proof.
  split.
  - intros [a na]; exact (na a).
  - intros e; exact (Empty_rec _ e).
Defined.
