(** * Basic facts about fibrations *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Definition base_path {A} {P : A -> Type} {u v : sigT P} :
  (u = v) -> (pr1 u = pr1 v) :=
  ap (@pr1 _ _).

(* *** Homotopy fibers *)

(** Homotopy fibers are homotopical inverse images of points.  *)

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

(** This lemma tells us how to extract a commutative triangle in the *)
(*    base from a path in the homotopy fiber. *)

Lemma hfiber_triangle {A B} {f : A -> B} {z : B} {x y : hfiber f z} (p : x = y) :
  (ap f (base_path p)) @ (y.2) = (x.2).
Proof.
  destruct p. simpl. auto with path_hints.
Defined.

(** The action of map on a function of two variables, one dependent on the other. *)

Lemma map_twovar {A : Type} {P : A->Type} {B : Type} {x y : A} {a : P x} {b : P y}
  (f : forall x : A, P x -> B) (p : x = y) (q : p # a = b) :
  f x a = f y b.
Proof.
  induction p.
  simpl in q.
  by induction q.
Defined.

Definition fiber_path {A} {P : A -> Type} {u v : sigT P}
  (p : u = v) : (transport _ (ap (@pr1 _ _) p) (u.2) = v.2).
Proof.
  by path_induction.
Defined.
(** 2-Paths in a total space. *)

Definition total_path {A} {P : A -> Type} {x y : sigT P} (p : x.1 = y.1) :
  (transport _ p (x.2) = y.2) -> (x = y).
Proof.
  intros q.
  destruct x as [x H].
  destruct y as [y G].
  simpl in * |- *.
  induction p.
  simpl in q.
  by path_induction.
Defined.


(** And these operations are inverses.  See [total_paths_equiv], later
   on, for a more precise statement. *)

Lemma total_path_reconstruction {A} {P:A->Type} {x y : sigT P} (p : x = y) :
  total_path (base_path p) (fiber_path p) = p.
Proof.
  induction p.
  by induction x.
Defined.

Lemma total_path2 {A} (P : A-> Type) (x y : sigT P)
  (p q : x = y) (r : base_path p = base_path q) :
  (transport (fun s => s # (x.2) = (y.2)) r (fiber_path p) = fiber_path q) -> (p = q).
Proof.
  intro H.
  transitivity (total_path _ (fiber_path p)) ;
  [ apply inverse, total_path_reconstruction | ].
  transitivity (total_path _ (fiber_path q)) ;
  [ | apply total_path_reconstruction ].
  by apply @map_twovar with
    (f := @total_path A P x y)
    (p := r).
Defined.

(** Transporting along a path between paths. *)

(* I cannot find trans_trans_opp
Lemma trans_trans_opp2 {A : Type} {P : A -> Type} {x y : A} {p q : x = y}
  (r : p = q) (z : P y) :
  trans_trans_opp p z =
  map (transport p) (trans2 (opposite2 r) z)
  @ trans2 r (q^ #  z)
  @ trans_trans_opp q z.
Proof.
  path_induction.
Defined. *)


(** *** Replacing a map with a fibration *)

Definition equiv_fibration_replacement  {B C} (f:C ->B):
  C <~> {y:B & hfiber f y}.
Proof.
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               C {y:B & {x:C & f x = y}}
               (fun c => (f c; (c; idpath)))
               (fun c => c.2.1)
               _
               (fun c => idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
Defined.

Definition hfiber_fibration {X} (x : X) (P:X->Type):
    P x <~> @hfiber (sigT P) X pr1 x.
Proof.
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               (P x) { z : sigT P & z.1 = x }
               (fun Px => ((x; Px); idpath))
               (fun Px => transport P Px.2 Px.1.2)
               _
               (fun Px => idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
Defined.
