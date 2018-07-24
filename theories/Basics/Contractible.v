(* -*- mode: coq; mode: visual-line -*- *)
(** Contractibility *)

Require Import Overture PathGroupoids.
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
    intro r; destruct r; symmetry; now apply concat_Vp.
  transitivity (path_contr x y);auto with path_hints.
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)
(** Because [Contr] is a notation, and [Contr_internal] is the record, we need to iota expand to fool Coq's typeclass machinery into accepting supposedly "mismatched" contexts. *)

Global Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
|} in c.

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

Definition path_basedpaths' {X : Type} {x y : X} (p : y = x)
: (x;1) = (y;p) :> {z:X & z=x}.
Proof.
  destruct p; reflexivity.
Defined.

Global Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x} | 100.
Proof.
  refine (BuildContr _ (x;1) _).
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
  := BuildContr _ (r (center X)) (fun y => (ap r (contr _)) @ h _).
