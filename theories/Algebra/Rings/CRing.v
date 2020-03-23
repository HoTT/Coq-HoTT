Require Import Basics Types.
Require Import WildCat.
Require Import Classes.interfaces.abstract_algebra.
Require Import Algebra.Groups.AbelianGroup.
Require Export Classes.theory.rings.

(** Theory of commutative rings *)

(** TODO: in reality we should really develop the theory of non-commutative rings seperately, and have commutative rings as a special case of that theory. Similar to how we have Group and AbGroup.

But since we are only interested in commutative rings for the time being, it makes sense to only consider them.
*)


(** A commutative ring consists of the following data *)
Record CRing := {
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

Arguments cring_type {_}.
Arguments cring_plus {_}.
Arguments cring_mult {_}.
Arguments cring_zero {_}.
Arguments cring_one {_}.
Arguments cring_negate {_}.
Arguments cring_isring {_}.

(** [issig_CRing] is a standard lemma associated with records which shows that a given record, in this case [CRing] is equivalent to a sigma type. We use records/classes because they are more performant than nested sigma types, especially ones this large. We have a special tactic [issig] that can automatically prove these kinds of lemmas so we only have to write succinct lemmas like this. *)
Definition issig_CRing : _ <~> CRing := ltac:(issig).

(** We coerce rings to their underlying type. *)
Coercion cring_type : CRing >-> Sortclass.
(** All fields which are typeclasses are global instances *)
Global Existing Instances cring_plus cring_mult cring_zero cring_one cring_negate cring_isring.

(** A ring homomorphism between commutative rings is a map of the underlying type and a proof that this map is a ring homomorphism. *)
Record CRingHomomorphism (A B : CRing) := {
  rng_homo_map : A -> B;
  rng_homo_ishomo : IsSemiRingPreserving rng_homo_map;
}.

Arguments Build_CRingHomomorphism {_ _} _ _.

Definition issig_CRingHomomorphism (A B : CRing)
  : _ <~> CRingHomomorphism A B
  := ltac:(issig).

(** We coerce ring homomorphisms to their underlyig maps *)
Coercion rng_homo_map : CRingHomomorphism >-> Funclass.
(** And we make rng_homo_ishomo a global instance. *)
Global Existing Instance rng_homo_ishomo.

Definition equiv_path_cringhomomorphism `{Funext} {A B : CRing}
  {f g : CRingHomomorphism A B} : f == g <~> f = g.
Proof.
  refine ((equiv_ap (issig_CRingHomomorphism A B)^-1 _ _)^-1 oE _).
  refine (equiv_path_sigma_hprop _ _ oE _).
  apply equiv_path_forall.
Defined.

Definition rng_homo_id (A : CRing) : CRingHomomorphism A A
  := Build_CRingHomomorphism idmap _.

Definition rng_homo_compose {A B C : CRing}
  (f : CRingHomomorphism B C) (g : CRingHomomorphism A B)
  : CRingHomomorphism A C.
Proof.
  snrapply Build_CRingHomomorphism.
  1: exact (f o g).
  rapply compose_sr_morphism.
Defined.

Lemma rng_dist_l {A : CRing} (a b c : A)
  : a * (b + c) = a * b + a * c.
Proof.
  rapply (simple_distribute_l a b c).
Defined.

Lemma rng_dist_r {A : CRing} (a b c : A)
  : (a + b) * c = a * c + b * c.
Proof.
  rapply (simple_distribute_r a b c).
Defined.

Definition rng_zero_mul {A : CRing} (a : A) : 0 * a = 0
  := left_absorb a.

Definition rng_mul_zero {A : CRing} (a : A) : a * 0 = 0
  := right_absorb a.

(** Underlying abelian groups of rings *)
Definition abgroup_cring : CRing -> AbGroup
  := fun A => Build_AbGroup A _ _ _ _.

Coercion abgroup_cring : CRing >-> AbGroup.

(** Wild category of commutative rings *)

Global Instance isgraph_cring : IsGraph CRing
  := Build_IsGraph _ CRingHomomorphism.

Global Instance is01cat_cring : Is01Cat CRing
  := Build_Is01Cat _ _ rng_homo_id (@rng_homo_compose).

Global Instance isgraph_cringhomomorphism {A B : CRing} : IsGraph (A $-> B)
  := induced_graph (@rng_homo_map A B).

Global Instance is01cat_cringhomomorphism {A B : CRing} : Is01Cat (A $-> B)
  := induced_01cat (@rng_homo_map A B).

Global Instance is0gpd_cringhomomorphism {A B : CRing}: Is0Gpd (A $-> B)
  := induced_0gpd (@rng_homo_map A B).

Global Instance is0functor_postcomp_cringhomomorphism {A B C : CRing} (h : B $-> C)
  : Is0Functor (@cat_postcomp CRing _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (ap h (p a)).
Defined.

Global Instance is0functor_precomp_cringhomomorphism
       {A B C : CRing} (h : A $-> B)
  : Is0Functor (@cat_precomp CRing _ _ A B C h).
Proof.
  apply Build_Is0Functor.
  intros [f ?] [g ?] p a ; exact (p (h a)).
Defined.

(** CRing forms a 1Cat *)
Global Instance is1cat_cring : Is1Cat CRing.
Proof.
  by rapply Build_Is1Cat.
Defined.

Global Instance hasmorext_cring `{Funext} : HasMorExt CRing.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  snrapply @isequiv_homotopic.
  1: exact (equiv_path_cringhomomorphism^-1%equiv).
  1: exact _.
  intros []; reflexivity. 
Defined.



