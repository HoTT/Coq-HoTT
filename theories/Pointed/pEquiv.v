Require Import Basics.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(* The pointed identity is a pointed equivalence *)
Definition pequiv_pmap_idmap {A} : A <~>* A
  := Build_pEquiv _ _ pmap_idmap _.

(* pointed equivalence is a reflexive relation *)
Global Instance pequiv_reflexive : Reflexive pEquiv.
Proof.
  intro; apply pequiv_pmap_idmap.
Defined.

(* This inverse equivalence of a pointed equivalence is again
   a pointed equivalence *)
Definition pequiv_inverse {A B} (f : A <~>* B) : B <~>* A.
Proof.
  serapply Build_pEquiv.
  1: apply (Build_pMap _ _ f^-1).
  1: apply moveR_equiv_V; symmetry; apply point_eq.
  exact _.
Defined.

Notation "f ^-1*" := (pequiv_inverse f) : pointed_scope.

(* pointed equivalence is a symmetric relation *)
Global Instance pequiv_symmetric : Symmetric pEquiv.
Proof.
  intros ? ?; apply pequiv_inverse.
Defined.

(* pointed equivalences compose *)
Definition pequiv_compose {A B C : pType} (f : A <~>* B) (g : B <~>* C)
  : A <~>* C := (Build_pEquiv A C (g o* f) isequiv_compose).

(* pointed equivalence is a transitive relation *)
Global Instance pequiv_transitive : Transitive pEquiv.
Proof.
  intros ? ? ?; apply pequiv_compose.
Defined.

Notation "g o*E f" := (pequiv_compose f g) : pointed_scope.

(* The record for pointed equivalences is equivalently a sigma type *)
Definition issig_pequiv (A B : pType)
  : { f : A <~> B & f (point A) = point B } <~> (A <~>* B).
Proof.
  transitivity { f : A ->* B & IsEquiv f }.
  2: issig.
  refine ((equiv_functor_sigma' (P := fun f => IsEquiv f.1)
    (issig_pmap A B) (fun f => equiv_idmap _)) oE _).
  refine (_ oE (equiv_functor_sigma' (Q := fun f => f.1 (point A) = point B)
    (issig_equiv A B)^-1 (fun f => equiv_idmap _))).
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  refine (equiv_sigma_assoc _ _ oE _).
  refine (equiv_functor_sigma' 1 _).
  intro; cbn; apply equiv_sigma_symm0.
Defined.

(* Sometimes we wish to construct a pEquiv from an equiv and a proof that it is pointed *)
Definition Build_pEquiv' {A B : pType} (f : A <~> B)
  (p : f (point A) = point B)
  : A <~>* B := Build_pEquiv _ _ (Build_pMap _ _ f p) _.

(* Under univalence, pointed equivalences are equivalent to paths *)
Definition equiv_path_ptype `{Univalence} (A B : pType) : A <~>* B <~> A = B.
Proof.
  destruct A as [A a], B as [B b].
  refine (equiv_ap issig_ptype (A;a) (B;b) oE _).
  refine (equiv_path_sigma _ _ _ oE _).
  refine (_ oE (issig_pequiv _ _)^-1); simpl.
  refine (equiv_functor_sigma' (equiv_path_universe A B) _); intros f.
  apply equiv_concat_l.
  apply transport_path_universe.
Defined.

Definition path_ptype `{Univalence} {A B : pType} : (A <~>* B) -> A = B
  := equiv_path_ptype A B.

Definition pequiv_path {A B : pType} : (A = B) -> (A <~>* B).
Proof.
  intros p; apply (ap issig_ptype^-1) in p.
  srefine (Build_pEquiv' (equiv_path A B p..1) p..2).
Defined.

(* A pointed version of Sect (sometimes useful for proofs of some equivalences) *)
Definition pSect {A B : pType} (s : A ->* B) (r : B ->* A)
  := r o* s ==* pmap_idmap.

Arguments pSect _ _ / _ _.

(* A pointed equivalence is a section of its inverse *)
Definition peissect {A B : pType} (f : A <~>* B) : pSect f f^-1*.
Proof.
  pointed_reduce.
  srefine (Build_pHomotopy _ _).
  1: apply (eissect f).
  pointed_reduce.
  unfold moveR_equiv_V.
  apply inverse, concat_1p.
Qed.

(* A pointed equivalence is a retraction of its inverse *)
Definition peisretr {A B : pType} (f : A <~>* B) : pSect f^-1* f.
Proof.
  srefine (Build_pHomotopy _ _).
  1: apply (eisretr f).
  pointed_reduce.
  unfold moveR_equiv_V.
  hott_simpl.
  apply eisadj.
Qed.

(* A version of equiv_adjointify for pointed equivalences
  where all data is pointed. There is a lot of unecessery data here
  but sometimes it is easier to prove equivalences using this. *)
Definition pequiv_adjointify {A B : pType} (f : A ->* B) (f' : B ->* A)
  (r : pSect f' f) (s : pSect f f') : A <~>* B.
Proof.
  serapply Build_pEquiv.
  1: assumption.
  serapply (isequiv_adjointify f f').
  1: apply r.
  apply s.
Defined.

(* In some situations you want the back and forth maps to be pointed
   but not the sections *)
Definition pequiv_adjointify' {A B : pType} (f : A ->* B) (f' : B ->* A)
  (r : Sect f' f) (s : Sect f f') : A <~>* B.
Proof.
  serapply Build_pEquiv.
  1: assumption.
  serapply (isequiv_adjointify f f').
  1: apply r.
  apply s.
Defined.