Require Import Basics Types.
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.AbelianGroup.
Require Export Classes.theory.rings.

(** Theory of commutative rings *)

(** TODO: in reality we should really develop the theory of non-commutative rings seperately, and have commutative rings as a special case of that theory. Similar to how we have Group and AbGroup.

But since 
*)


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

(** [issig_CRing] is a standard lemma associated with records which shows that a given record, in this case [CRing] is equivalent to a sigma type. We use records/classes because they are more performant than nested sigma types, especially ones this large. We have a special tactic [issig] that can automatically prove these kinds of lemmas so we only have to write succinct lemmas like this. *)
Definition issig_CRing : _ <~> CRing := ltac:(issig).

(** We coerce rings to their underlying type. *)
Coercion cring_type : CRing >-> Sortclass.
(** All fields which are typeclasses are global instances *)
Global Existing Instances cring_plus cring_mult cring_zero cring_one cring_negate cring_isring.

(** A ring homomorphism between commutative rings is a map of the underlying type and a proof that this map is a ring homomorphism. *)
Class CRingHomomorphism (A B : CRing) := {
  rng_homo_map : A -> B;
  rng_homo_ishomo : IsSemiRingPreserving rng_homo_map;
}.

Definition issig_CRingHomomorphism {A B : CRing} : _ <~> CRingHomomorphism A B
  := ltac:(issig).

(** We coerce ring homomorphisms to their underlyig maps *)
Coercion rng_homo_map : CRingHomomorphism >-> Funclass.
(** And we make rng_homo_ishomo a global instance. *)
Global Existing Instance rng_homo_ishomo.

Definition rng_homo_compose {A B C : CRing}
  (f : CRingHomomorphism B C) (g : CRingHomomorphism A B)
  : CRingHomomorphism A C.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact (f o g).
  rapply compose_sr_morphism.
Defined.



