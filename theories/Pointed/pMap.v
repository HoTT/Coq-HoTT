Require Import Basics Types PathAny FunextVarieties.
Require Import Pointed.Core.
Require Import Pointed.pHomotopy.

Local Open Scope pointed_scope.

(* By function extensionality pointed homotopies are equivalent to paths *)
Definition equiv_path_pmap `{Funext} {A B : pType} (f g : A ->* B)
  : (f ==* g) <~> (f = g).
Proof.
  refine (_ oE (issig_phomotopy f g)^-1).
  revert f g; apply (equiv_path_issig_contr (issig_pmap A B)).
  { intros [f feq]; cbn.
    exists (fun a => 1%path).
    apply concat_1p. }
  intros [f feq]; cbn.
  contr_sigsig f (fun a:A => idpath (f a)); cbn.
  refine (contr_equiv' {feq' : f (point A) = point B & feq = feq'} _).
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros p.
  refine (equiv_path_inverse _ _ oE _).
  apply equiv_concat_r. symmetry; apply concat_1p.
Defined.

Definition path_pmap `{Funext} {A B : pType} {f g : A ->* B}
  : (f ==* g) -> (f = g) := equiv_path_pmap f g.

(* We note that the inverse of [path_pmap] computes definitionally on reflexivity, and hence [path_pmap] itself computes typally so.  *)
Definition equiv_inverse_path_pmap_1 `{Funext} {A B} {f : A ->* B}
  : (equiv_path_pmap f f)^-1 1%path = reflexivity f
  := 1.

Definition equiv_path_pmap_1 `{Funext} {A B} {f : A ->* B}
  : path_pmap (reflexivity f) = 1%path.
Proof.
  apply moveR_equiv_M.
  reflexivity.
Defined.

(** ** Associativity of pointed map composition *)

Definition pmap_compose_assoc {A B C D : pType} (h : C ->* D)
  (g : B ->* C) (f : A ->* B) : (h o* g) o* f ==* h o* (g o* f).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap o* f ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

(** ** Trivially pointed maps *)

(** Not infrequently we have a map between two unpointed types and want to consider it as a pointed map that trivially respects some given point in the domain. *)
Definition pmap_from_point {A B : Type} (f : A -> B) (a : A)
  := Build_pMap (Build_pType A a) (Build_pType B (f a)) f 1%path.
