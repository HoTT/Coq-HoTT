Require Import Basics.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

Global Instance phomotopy_reflexive {A B} : Reflexive (@pHomotopy A B).
Proof.
  intro.
  serapply Build_pHomotopy.
  + intro. reflexivity.
  + apply concat_1p.
Defined.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
           (h : B ->* C) (p : f ==* g)
: h o* f ==* h o* g.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply ap, p.
  - reflexivity.
Qed.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
           {g h : B ->* C} (p : g ==* h)
: g o* f ==* h o* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply p.
  - refine (concat_p1 _ @ (concat_1p _)^).
Qed.

(** ** Composition of pointed homotopies *)

Definition phomotopy_compose {A B : pType} {f g h : A ->* B}
           (p : f ==* g) (q : g ==* h)
: f ==* h.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact (p x @ q x).
  - apply concat_p1.
Qed.

Infix "@*" := phomotopy_compose : pointed_scope.

Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.

Definition phomotopy_inverse {A B : pType} {f g : A ->* B}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - apply concat_Vp.
Qed.

Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B)
  := @phomotopy_inverse A B.


Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.

Definition issig_phomotopy {A B : pType} (f g : A ->* B)
: { p : f == g & p (point A) @ point_eq g = point_eq f } <~> (f ==* g).
Proof.
  issig (@Build_pHomotopy A B f g) (@pointed_htpy A B f g) (@point_htpy A B f g).
Defined.


