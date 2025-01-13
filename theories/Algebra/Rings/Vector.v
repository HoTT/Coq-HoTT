Require Import Basics.Overture Basics.Trunc Basics.Tactics Basics.PathGroupoids.
Require Import Types.Sigma.
Require Import Algebra.AbGroups.AbelianGroup Algebra.Rings.Ring Algebra.Rings.Module.
Require Import Spaces.Nat.Core.
Require Import Spaces.List.Core Spaces.List.Theory Spaces.List.Paths.
Require Import abstract_algebra.

Local Open Scope mc_scope.

Local Set Universe Minimization ToSet.
Local Set Polymorphic Inductive Cumulativity.

(** * Vectors *)

(** A vector is simply a list with a specified length. This data structure has many uses, but here we will focus on lists of left module elements. *)

(** ** Definition *)

Definition Vector@{i|} (A : Type@{i}) (n : nat) : Type@{i}
  := { l : list A & length l = n }.

(** *** Constructors *)

Definition Build_Vector (A : Type) (n : nat)
  (f : forall (i : nat), (i < n)%nat -> A)
  : Vector A n
  := (Build_list n f; length_Build_list n f).

(** *** Projections *)

Definition entry {A : Type} {n : nat} (v : Vector A n) i {Hi : (i < n)%nat} : A
  := nth' (pr1 v) i ((pr2 v)^ # Hi).

(** *** Basic properties *)

Definition entry_Build_Vector {A : Type} {n}
  (f : forall (i : nat), (i < n)%nat -> A) i {Hi : (i < n)%nat}
  : entry (Build_Vector A n f) i = f i Hi.
Proof.
  snrapply nth'_Build_list.
Defined.

Global Instance istrunc_vector@{i} (A : Type@{i}) (n : nat) k `{IsTrunc k.+2 A}
  : IsTrunc k.+2 (Vector A n).
Proof.
  rapply istrunc_sigma@{i i i}.
Defined.

Definition path_vector@{i} (A : Type@{i}) {n : nat} (v1 v2 : Vector@{i} A n)
  (H : forall i (H : (i < n)%nat), entry v1 i = entry v2 i)
  : v1 = v2.
Proof.
  rapply path_sigma_hprop@{i i i}.
  snrapply path_list_nth'.
  1: exact (pr2 v1 @ (pr2 v2)^).
  intros i Hi.
  snrefine (_ @ H i (pr2 v1 # Hi) @ _).
  1, 2: apply nth'_nth'.
Defined.

Definition path_entry_vector {A : Type} {n : nat} (v : Vector A n)
  (i j : nat) (Hi : (i < n)%nat) (Hj : (j < n)%nat) (p : i = j)
  : entry v i = entry v j.
Proof.
  destruct p.
  apply nth'_nth'.
Defined.

(** ** Operations *)

Definition vector_map {A B : Type} {n} (f : A -> B)
  : Vector A n -> Vector B n
  := fun v => Build_Vector B n (fun i _ => f (entry v i)).

Definition vector_map2 {A B C : Type} {n} (f : A -> B -> C)
  : Vector A n -> Vector B n -> Vector C n
  := fun v1 v2 => Build_Vector C n (fun i _ => f (entry v1 i) (entry v2 i)).

(** ** Abelian group structure *)

Section VectorAddition.

  Context (A : AbGroup) (n : nat).

  Definition vector_plus : Plus (Vector A n) := vector_map2 (+).

  Definition vector_zero : Zero (Vector A n)
    := Build_Vector A n (fun _ _ => 0).

  Definition vector_neg : Negate (Vector A n) := vector_map (-).

  Definition associative_vector_plus : Associative vector_plus.
  Proof.
    intros v1 v2 v3; apply path_vector; intros i Hi.
    rewrite 4 entry_Build_Vector.
    apply associativity.
  Defined.
  
  Definition commutative_vector_plus : Commutative vector_plus.
  Proof.
    intros v1 v2; apply path_vector; intros i Hi.
    rewrite 2 entry_Build_Vector.
    apply commutativity.
  Defined.

  Definition left_identity_vector_plus : LeftIdentity vector_plus vector_zero.
  Proof.
    intros v; apply path_vector; intros i Hi.
    rewrite 2 entry_Build_Vector.
    apply left_identity.
  Defined.

  Definition right_identity_vector_plus : RightIdentity vector_plus vector_zero.
  Proof.
    intros v; apply path_vector; intros i Hi.
    rewrite 2 entry_Build_Vector.
    apply right_identity.
  Defined.

  Definition left_inverse_vector_plus
    : LeftInverse vector_plus vector_neg vector_zero.
  Proof.
    intros v; apply path_vector; intros i Hi.
    rewrite 3 entry_Build_Vector.
    apply left_inverse.
  Defined.

  Definition right_inverse_vector_plus
    : RightInverse vector_plus vector_neg vector_zero.
  Proof.
    intros v; apply path_vector; intros i Hi.
    rewrite 3 entry_Build_Vector.
    apply right_inverse.
  Defined.

  Definition abgroup_vector : AbGroup.
  Proof.
    snrapply Build_AbGroup.
    1: snrapply Build_Group.
    5: repeat split.
    - exact (Vector A n).
    - exact vector_plus.
    - exact vector_zero.
    - exact vector_neg.
    - exact _.
    - exact associative_vector_plus.
    - exact left_identity_vector_plus.
    - exact right_identity_vector_plus.
    - exact left_inverse_vector_plus.
    - exact right_inverse_vector_plus.
    - exact commutative_vector_plus.
  Defined.

End VectorAddition.

Arguments vector_plus {A n} v1 v2.

(** ** Module structure *)

Section VectorScale.
  (** A vector of elements of an R-module is itself an R-module. A special case is when the R-module is the ring R itself. *)
  Context (M : AbGroup) (n : nat) {R : Ring} `{IsLeftModule R M}.

  Definition vector_lact (r : R) : Vector M n -> Vector M n
    := vector_map (lact r).
  
  Definition left_heterodistribute_vector_lact_plus
    : LeftHeteroDistribute vector_lact vector_plus vector_plus.
  Proof.
    intros r v1 v2; apply path_vector; intros i Hi.
    rewrite 5 entry_Build_Vector.
    apply distribute_l.
  Defined.

  Definition right_heterodistribute_vector_lact_plus
    : RightHeteroDistribute vector_lact (+) vector_plus.
  Proof.
    intros r1 r2 v; apply path_vector; intros i Hi.
    rewrite 4 entry_Build_Vector.
    apply distribute_r.
  Defined.

  Definition heteroassociative_vector_lact_plus
    : HeteroAssociative vector_lact vector_lact vector_lact (.*.).
  Proof.
    intros r s v; apply path_vector; intros i Hi.
    rewrite 3 entry_Build_Vector.
    apply associativity.
  Defined.

  Definition left_identity_vector_lact : LeftIdentity vector_lact 1.
  Proof.
    intros v; apply path_vector; intros i Hi.
    rewrite entry_Build_Vector.
    apply left_identity.
  Defined.

  Definition isleftmodule_isleftmodule_vector
    : IsLeftModule R (abgroup_vector M n).
  Proof.
    snrapply Build_IsLeftModule.
    - exact vector_lact.
    - exact left_heterodistribute_vector_lact_plus.
    - exact right_heterodistribute_vector_lact_plus.
    - exact heteroassociative_vector_lact_plus.
    - exact left_identity_vector_lact.
  Defined.

End VectorScale.

Arguments vector_lact {M n R _} r v.
