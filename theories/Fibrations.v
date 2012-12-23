(** * Basic facts about fibrations *)

Require Import Overture.
Local Open Scope path_scope.

(*

(* *** Homotopy fibers *)

(** Homotopy fibers are homotopical inverse images of points.  *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

(** This lemma tells us how to extract a commutative triangle in the *)
(*    base from a path in the homotopy fiber. *)

Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x = y) :
  (map f (base_path p)) @ (pr2 y) = (pr2 x).
Proof.
  destruct p.
Defined.

(** The action of map on a function of two variables, one dependent on the other. *)

Lemma map_twovar {A : Type} {P : fibration A} {B : Type} {x y : A} {a : P x} {b : P y}
  (f : forall x : A, P x -> B) (p : x = y) (q : p # a = b) :
  f x a = f y b.
Proof.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Defined.

(** 2-Paths in a total space. *)

Lemma total_path2 (A : Type) (P : fibration A) (x y : total P)
  (p q : x = y) (r : base_path p = base_path q) :
  (transport (P := fun s => s # pr2 x = pr2 y) r (fiber_path p) = fiber_path q) -> (p = q).
Proof.
  intro H.
  path_via (total_path (fiber_path p)) ;
  [ apply opposite, total_path_reconstruction | ].
  path_via (total_path (fiber_path q)) ;
  [ | apply total_path_reconstruction ].
  apply @map_twovar with
    (f := @total_path A P x y)
    (p := r).
  assumption.
Defined.

(** Transporting along a path between paths. *)

Lemma trans_trans_opp2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P y) :
  trans_trans_opp p z =
  map (transport p) (trans2 (opposite2 r) z)
  @ trans2 r (^q #  z)
  @ trans_trans_opp q z.
Proof.
  path_induction.
Defined.

(** Transporting in a fibration of paths. *)

Lemma trans_paths A B (f g : A -> B) (x y : A) (p : x = y) (q : f x = g x) :
  transport (P := fun a => f a = g a) p q
  =
  ^map f p @ q @ map g p.
Proof.
  path_induction.
  hott_simpl.
Defined.
*)
