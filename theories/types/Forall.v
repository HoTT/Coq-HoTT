(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about dependent products *)

Require Import Overture Contractible Equivalences.
Require Export Funext.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** *** Paths *)

(** See [Funext] for the formulation of function extensionality. *)

(** Now we show how these things compute. *)

Definition apD10_path_forall `{FunextAxiom} {A : Type} {B : A -> Type}
  (f g : forall x:A, B x) (h : forall x:A, f x = g x)
  : apD10 (path_forall _ _ h) = h
  := eisretr apD10 h.

Definition eta_path_forall `{FunextAxiom} {A : Type} {B : A -> Type}
  (f g : forall x:A, B x) (p : f = g)
  : path_forall _ _ (apD10 p) = p
  := eissect apD10 p.

(** The identification of the path space of a dependent function space, up to equivalence, is of course just funext. *)

Instance isequiv_path_forall `{FunextAxiom} {A : Type} {B : A -> Type}
  (f g : forall x:A, B x)
  : IsEquiv (path_forall f g)
  := @isequiv_inverse _ _ (@apD10 A B f g) _.

Definition equiv_path_forall `{FunextAxiom} {A : Type} {B : A -> Type}
  (f g : forall x:A, B x)
  : (forall x:A, f x = g x)  <~>  (f = g)
  := @equiv_inverse (f = g) _ (@apD10 A B f g) _.

(** *** Transport *)

(** The concrete description of transport in sigmas and pis is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require the full Id-elim rule by way of "dependent transport" [transportD].

  In particular this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)

Lemma transport_forall_unwound
  {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B x1, C x1 y) 
  : forall y : B x2, C x2 y.
Proof.
  intro y.
  pose (z0 := f (p^ # y)).
  pose (z1 := transportD _ _ p _ z0).
  apply (fun p => transport (C x2) p z1).
  path_via (transport B (p^ @ p) y).
    symmetry.  apply transport_pp.  
    apply (fun e => @ap (x2=x2) (B x2) (fun q => transport B q y) 
                      (p^ @ p) 1e).
  apply concat_Vp.
Defined.

(* Note: conclusion should be [==] if that is defined in an earlier file. *) 
Definition transport_forall
  {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B x1, C x1 y) 
  : forall y : B x2,
    (transport (fun x => forall y:B x, C x y) p f) y
  = (transport_forall_unwound p f) y.
Proof.
  destruct p.  auto.
Defined.

(** *** HLevel *)


(** *** Functorial action *)


(** *** Equivalences *)

