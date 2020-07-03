Require Import Basics Types.
Require Import Algebra.Rings.CRing.
Require Import Algebra.AbGroups.

Local Open Scope mc_scope.

(** In this file we define Ideals *)

(** TODO: In the future it might be useful to define ideals as submodules *)

(** An additive subgroup I of a ring R is an ideal when: *)
Class IsIdeal {R : CRing} (I : Subgroup R) := {
  (** Forall r : R and x : I, there exists an a : I, such that a = r * x inside R *)
  isideal (r : R) (x : I)
    : exists (a : I), issubgroup_incl a = r * issubgroup_incl x;
}.

Record Ideal (R : CRing) := {
  ideal_subgroup : Subgroup R;
  ideal_isideal : IsIdeal ideal_subgroup;
}.

Coercion ideal_subgroup : Ideal >-> Subgroup.
Global Existing Instances ideal_isideal.


Global Instance issubgroup_trivial {G : Group} : IsSubgroup TrivialAbGroup G.
Proof.
  snrapply Build_IsSubgroup.
  { snrapply (Build_GroupHomomorphism (fun _ => group_unit)).
    intros ??; symmetry; apply left_identity. }
  cbn; intros ???.
  apply path_unit.
Defined.

Global Instance isinj_idmap A : @IsInjective A A idmap
  := fun x y => idmap.

Global Instance issubgroup_group {G : Group} : IsSubgroup G G
  := Build_IsSubgroup _ _ grp_homo_id _.

Definition trivial_subgroup {G} : Subgroup G
  := Build_Subgroup G TrivialAbGroup _.

Definition trivial_subgroup' {G} : Subgroup G
  := Build_Subgroup G G _.

Section Examples.

  Context (R : CRing).

  (** The zero ideal is an ideal *)
  Global Instance isideal_trivial_subgroup
    : IsIdeal (R:=R) trivial_subgroup.
  Proof.
    split.
    intros r [].
    exists tt.
    refine (_ @ _^ @ ap _ _^).
    1,3: rapply grp_homo_unit.
    apply rng_mult_zero_r.
  Defined.

  (** Zero ideal *)
  Definition ideal_zero : Ideal R
    := Build_Ideal R _ isideal_trivial_subgroup.

  (** The unit ideal is an ideal *)
  Global Instance isideal_trivial_subgroup'
    : IsIdeal (R:=R) trivial_subgroup'.
  Proof.
    split.
    cbn; intros r r'.
    exists (r * r').
    reflexivity.
  Defined.

  (** Unit ideal *)
  Definition ideal_unit : Ideal R
    := Build_Ideal R _ isideal_trivial_subgroup'.

(** TODO: Intersection of ideals *)

(** TODO: Sum of ideals *)

(** TODO: Product of ideals *)

End Examples.

Definition ideal_kernel {R S : CRing} (f : CRingHomomorphism R S) : Ideal R.
Proof.
  snrapply Build_Ideal.
  1: exact (grp_kernel f).
  snrapply Build_IsIdeal.
  intros r x.
  simpl in x.
  unfold hfiber in x.
  srefine (_;_).
  { exists (r * x.1).
    refine (rng_homo_mult f _ _ @ _).
    refine (ap _ _ @ rng_mult_zero_r (f r)).
    exact x.2. }
  reflexivity.
Defined.

(** Properties of ideals *)

(** TODO: Maximal ideals *)
(** TODO: Principal ideal *)
(** TODO: Prime ideals *)
(** TODO: Radical ideals *)
(** TODO: Minimal ideals *)
(** TODO: Primary ideals *)

