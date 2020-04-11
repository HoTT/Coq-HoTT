Require Import Basics.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(* pointed homotopy is a reflexive relation *)
Global Instance phomotopy_reflexive {A B} : Reflexive (@pHomotopy A B).
Proof.
  intro.
  srapply Build_pHomotopy.
  + intro. reflexivity.
  + apply concat_1p.
Defined.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
Proof.
  pointed_reduce'.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply ap, p.
  - apply whiskerR.
    apply ap.
    symmetry.
    apply concat_p1.
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h) : g o* f ==* h o* f.
Proof.
  pointed_reduce'.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply p.
  - symmetry; apply concat_1p.
Defined.

(** ** Composition of pointed homotopies *)

Definition phomotopy_compose {A B : pType} {f g h : A ->* B}
  (p : f ==* g) (q : g ==* h) : f ==* h.
Proof.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((pointed_htpy p) x @ (pointed_htpy q) x).
  - simpl.
    refine (concat_pp_p _ _ _ @ _).
    refine (whiskerL _ (point_htpy q) @ _).
    exact (point_htpy p).
Defined.

Infix "@*" := phomotopy_compose : pointed_scope.

(* pointed homotopy is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.

Definition phomotopy_inverse {A B : pType} {f g : A ->* B}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; pointed_reduce'.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - apply concat_V_pp.
Defined.

(* pointed homotopy is a symmetric relation *)
Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B)
  := @phomotopy_inverse A B.


Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.

Definition issig_phomotopy {A B : pType} (f g : A ->* B)
: { p : f == g & p (point A) @ point_eq g = point_eq f } <~> (f ==* g).
Proof.
  issig.
Defined.

