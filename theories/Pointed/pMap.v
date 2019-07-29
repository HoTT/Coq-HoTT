Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pHomotopy.

Local Open Scope pointed_scope.

Definition equiv_path_pmap `{Funext} {A B : pType} (f g : A ->* B)
: (f ==* g) <~> (f = g).
Proof.
  refine ((equiv_ap' (issig_pmap A B)^-1 f g)^-1 oE _); cbn.
  refine (_ oE (issig_phomotopy f g)^-1).
  refine (equiv_path_sigma _ _ _ oE _); cbn.
  refine (equiv_functor_sigma' (equiv_path_arrow f g) _); intros p. cbn.
  refine (_ oE equiv_moveL_Vp _ _ _).
  refine (_ oE equiv_path_inverse _ _).
  apply equiv_concat_l.
  refine (transport_paths_Fl (path_forall f g p) (point_eq f) @ _).
  apply whiskerR, inverse2.
  refine (ap_apply_l (path_forall f g p) (point A) @ _).
  apply ap10_path_forall.
Defined.

Definition path_pmap `{Funext} {A B : pType} {f g : A ->* B}
: (f ==* g) -> (f = g)
  := equiv_path_pmap f g.


(** ** Associativity of pointed map composition *)

Definition pmap_compose_assoc {A B C D : pType}
           (h : C ->* D) (g : B ->* C) (f : A ->* B)
: (h o* g) o* f ==* h o* (g o* f).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap A ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap B o* f ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.