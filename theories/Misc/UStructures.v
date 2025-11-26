(** * Uniform Structures *)

From HoTT Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.

Local Open Scope nat_scope.

(** ** [nat]-graded uniform structures *)

(** A uniform structure on a type consists of an equivalence relation for every natural number, each one being stronger than its predecessor. *)
Class UStructure (us_type : Type) := {
  us_rel : nat -> Relation us_type;
  us_reflexive :: forall n : nat, Reflexive (us_rel n);
  us_symmetric :: forall n : nat, Symmetric (us_rel n);
  us_transitive :: forall n : nat, Transitive (us_rel n);
  us_pred : forall (n : nat) (x y : us_type), us_rel n.+1 x y -> us_rel n x y
}.

Notation "u =[ n ] v" := (us_rel n u v)
  (at level 70, format "u  =[ n ]  v").

Definition us_rel_leq {X : Type} {struct : UStructure X}
  {m n : nat} (hm : m <= n) {u v : X} (h : u =[n] v)
  : u =[m] v.
Proof.
  induction hm.
  - assumption.
  - apply IHhm.
    by apply us_pred.
Defined.

(** Every type admits the trivial uniform structure with the standard identity type on every level. *)
Instance trivial_us {X : Type} : UStructure X | 100.
Proof.
  srapply (Build_UStructure _ (fun n x y => (x = y))).
  exact (fun _ _ _ => idmap).
Defined.

(** Example of a uniform structures based on truncations, with the relation being the [n-2]-truncation of the identity type. *)
Definition trunc_us {X : Type} : UStructure X.
Proof.
  srapply (Build_UStructure X
            (fun n x y => Tr (trunc_index_inc (-2) n) (x = y))).
  - intros n x. exact (tr idpath).
  - intros n x y h; strip_truncations.
    exact (tr h^).
  - intros n x y z h1 h2; strip_truncations.
    exact (tr (h1 @ h2)).
  - intros n x y h; strip_truncations.
    exact (tr h).
Defined.

(** ** Continuity *)

(** Definition of a continuous function depending on two uniform structures. *)
Definition IsContinuous
  {X Y : Type} {usX : UStructure X} {usY : UStructure Y} (p : X -> Y)
  := forall (u : X) (m : nat),
      {n : nat & forall v : X, u =[n] v -> p u =[m] p v}.

Definition uniformly_continuous {X Y : Type}
  {usX : UStructure X} {usY : UStructure Y} (p : X -> Y)
  := forall (m : nat),
      {n : nat & forall u v : X, u =[n] v -> p u =[m] p v}.

(** In the case that the target has the trivial uniform structure, it is useful to state uniform continuity by providing the specific modulus, which now only depends on the function. *)
Definition is_modulus_of_uniform_continuity {X Y : Type} {usX : UStructure X}
  (n : nat) (p : X -> Y)
  := forall u v : X, u =[n] v -> p u = p v.

Definition uniformly_continuous_has_modulus {X Y :Type} {usX : UStructure X}
  {p : X -> Y} {n : nat} (c : is_modulus_of_uniform_continuity n p)
  : uniformly_continuous p
  := fun m => (n; c).

Definition iscontinuous_uniformly_continuous {X Y : Type}
  {usX : UStructure X} {usY : UStructure Y} (p : X -> Y)
  : uniformly_continuous p -> IsContinuous p
  := fun uc u m => ((uc m).1 ; fun v => (uc m).2 u v).
