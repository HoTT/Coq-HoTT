(* -*- mode: coq; mode: visual-line -*- *)
(** Contractibility *)

Require Import HoTT.Basics.Overture HoTT.Basics.PathGroupoids.
Local Open Scope path_scope.

(** Naming convention: we consistently abbreviate "contractible" as "contr".  A theorem about a space [X] being contractible (which will usually be an instance of the typeclass [Contr]) is called [contr_X]. *)

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
Generalizable Variables A B f.

(** If a space is contractible, then any two points in it are connected by a path in a canonical way. *)
Definition path_contr `{Contr A} (x y : A) : x = y
  := (contr x)^ @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
  - intro r; destruct r; symmetry; now apply concat_Vp.
  - transitivity (path_contr x y);auto with path_hints.
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)

Global Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) | 10000.
Proof.
  exists ((contr x)^ @ contr y).
  exact (path2_contr ((contr x)^ @ contr y)).
Defined.

(** Also, the total space of any based path space is contractible.  We define the [contr] fields as separate definitions, so that we can give them [simpl nomatch] annotations. *)

Definition path_basedpaths {X : Type} {x y : X} (p : x = y)
: (x;1) = (y;p) :> {z:X & x=z}.
Proof.
  destruct p; reflexivity.
Defined.

Arguments path_basedpaths {X x y} p : simpl nomatch.

Global Instance contr_basedpaths {X : Type} (x : X) : Contr {y : X & x = y} | 100.
Proof.
  exists (x ; 1).
  intros [y p]; apply path_basedpaths.
Defined.

(* Sometimes we end up with a sigma of a one-sided path type that's not eta-expanded, which Coq doesn't seem able to match with the previous instance. *)
Global Instance contr_basedpaths_etashort {X : Type} (x : X) : Contr (sig (@paths X x)) | 100
  := contr_basedpaths x.

Definition path_basedpaths' {X : Type} {x y : X} (p : y = x)
: (x;1) = (y;p) :> {z:X & z=x}.
Proof.
  destruct p; reflexivity.
Defined.

Global Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x} | 100.
Proof.
  refine (Build_Contr _ (x;1) _).
  intros [y p]; apply path_basedpaths'.
Defined.

Arguments path_basedpaths' {X x y} p : simpl nomatch.

(** Some useful computation laws for based path spaces *)

Definition ap_pr1_path_contr_basedpaths {X : Type}
           {x y z : X} (p : x = y) (q : x = z)
: ap pr1 (path_contr ((y;p):{y':X & x = y'}) (z;q)) = p^ @ q.
Proof.
  destruct p,q; reflexivity.
Defined.

Definition ap_pr1_path_contr_basedpaths' {X : Type}
           {x y z : X} (p : y = x) (q : z = x)
: ap pr1 (path_contr ((y;p):{y':X & y' = x}) (z;q)) = p @ q^.
Proof.
  destruct p,q; reflexivity.
Defined.

Definition ap_pr1_path_basedpaths {X : Type}
           {x y : X} (p : x = y)
: ap pr1 (path_basedpaths p) = p.
Proof.
  destruct p; reflexivity.
Defined.

Definition ap_pr1_path_basedpaths' {X : Type}
           {x y : X} (p : y = x)
: ap pr1 (path_basedpaths' p) = p^.
Proof.
  destruct p; reflexivity.
Defined.

(** If the domain is contractible, the function is propositionally constant. *)
Definition contr_dom_equiv {A B} (f : A -> B) `{Contr A} : forall x y : A, f x = f y
  := fun x y => ap f ((contr x)^ @ contr y).

(** Any retract of a contractible type is contractible *)
Definition contr_retract {X Y : Type} `{Contr X} 
           (r : X -> Y) (s : Y -> X) (h : forall y, r (s y) = y)
  : Contr Y
  := Build_Contr _ (r (center X)) (fun y => (ap r (contr _)) @ h _).

(** Sometimes the easiest way to prove that a type is contractible doesn't produce the definitionally-simplest center.  (In particular, this can affect performance, as Coq spends a long time tracing through long proofs of contractibility to find the center.)  So we give a way to modify the center. *)
Definition contr_change_center {A : Type} (a : A) `{Contr A}
  : Contr A.
Proof.
  exists a.
  intros; apply path_contr.
Defined.

(** If a type is contractible, then so is its type of contractions. *)
Global Instance contr_contr `{Funext} (A : Type) `{Contr A}
  : Contr (Contr A) | 100.
Proof.
  exists _; intros [a2 c2].
  destruct (contr a2).
  apply (ap (Build_Contr _ (center A))).
  apply path_forall; intros x.
  apply path2_contr.
Defined.
