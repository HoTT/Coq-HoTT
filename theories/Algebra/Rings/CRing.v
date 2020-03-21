Require Import Basics Types.
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.AbelianGroup.

(** Theory of commutative rings *)

(** A commutative ring consists of the following data *)
Class CRing := {
  (** A type *)
  cring_type : Type;
  (** A plus operation *)
  cring_plus : Plus cring_type;
  (** A mult operation *)
  cring_mult : Mult cring_type;
  (** A zero *)
  cring_zero : Zero cring_type;
  (** A one *)
  cring_one  : One  cring_type;
  (** A negation *)
  cring_negate : Negate cring_type;
  (** Such that this data satisfies the axioms of a commmutative ring. *)
  cring_isring : IsRing cring_type;
}.

(** We coerce rings to their underlying type. *)
Coercion cring_type : CRing >-> Sortclass.
(** All fields which are typeclasses are global instances *)
Global Existing Instances cring_plus cring_mult cring_zero cring_one cring_negate cring_isring.

(** A ring homomorphism between commutative rings is a map of the underlying type and a proof that this map is a ring homomorphism. *)
Class CRingHomomorphism (A B : CRing) := {
  rng_homo_map : A -> B;
  rng_homo_ishomo : IsSemiRingPreserving rng_homo_map;
}.







