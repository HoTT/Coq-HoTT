(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about dependent products *)

Require Import Overture PathGroupoids Contractible Equivalences.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** *** Paths *)

(** See [Funext] for the formulation of function extensionality. *)

(** Now we show how these things compute. *)

Definition apD10_path_forall `{Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) (h : forall x, f x = g x) :
  apD10 (path_forall _ _ h) = h
  := eisretr apD10 h.

Definition eta_path_forall `{Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) (p : f = g) :
  path_forall _ _ (apD10 p) = p
  := eissect apD10 p.

(** The identification of the path space of a dependent function space, up to equivalence, is of course just funext. *)

Instance isequiv_path_forall `{Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) :
  IsEquiv (path_forall f g)
  := @isequiv_inverse _ _ (@apD10 A P f g) _.

Definition equiv_path_forall `{E : Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) :
  (forall x, f x = g x)  <~>  (f = g).
Proof.
  apply symmetry.
  exists (@apD10 A P f g).
  apply E.
Defined.

(** *** Transport *)

(** The concrete description of transport in sigmas and pis is rather trickier than in the other types. In particular, these cannot be described just in terms of transport in simpler types; they require the full Id-elim rule by way of "dependent transport" [transportD].

  In particular this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory). A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)

(* Note: conclusion should be [==] if that is defined in an earlier file. *) 
Definition transport_forall
    {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
    {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y) :
  forall y : P x2,
    (transport (fun x => forall y : P x, C x y) p f) y =
    transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p^ # y)))
  := match p with idpath => fun _ => 1 end.


(** *** Functorial action *)


(** *** Equivalences *)
