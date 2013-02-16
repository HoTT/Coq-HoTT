(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about dependent products *)

Require Import Overture PathGroupoids Contractible Equivalences.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** *** Paths *)

(** Paths [p : f = g] in a function type [forall x:X, P x] are equivalent to functions taking values in path types, [H : forall x:X, f x = g x], or concisely, [H : f == g].

This equivalence, however, is just the combination of [apD10] and function extensionality [funext], and as such, [path_forall], et seq. are given in the [Overture]:  *)

(** Now we show how these things compute. *)

Definition apD10_path_forall `{Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) (h : f == g)
  : apD10 (path_forall _ _ h) = h
:= eisretr apD10 h.

Definition eta_path_forall `{Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) (p : f = g)
  : path_forall _ _ (apD10 p) = p
:= eissect apD10 p.

Definition path_forall_1 `{Funext} {A : Type} {P : A -> Type}
    (f : forall x, P x)
  : (path_forall f f (fun x => 1)) = 1
:= eta_path_forall f f 1.

(** The identification of the path space of a dependent function space, up to equivalence, is of course just funext. *)

Instance isequiv_path_forall `{Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) :
  IsEquiv (path_forall f g)
  := @isequiv_inverse _ _ (@apD10 A P f g) _.

Definition equiv_path_forall `{E : Funext} {A : Type} {P : A -> Type}
    (f g : forall x, P x) :
  (f == g)  <~>  (f = g).
Proof.
  apply symmetry.
  exists (@apD10 A P f g).
  apply E.
Defined.

(** *** Transport *)

(** The concrete description of transport in sigmas and pis is rather trickier than in the other types. In particular, these cannot be described just in terms of transport in simpler types; they require the full Id-elim rule by way of "dependent transport" [transportD].

  In particular this indicates why "transport" alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type Theory). A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? *)
Definition transport_forall
    {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
    {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y)
  : (transport (fun x => forall y : P x, C x y) p f) 
    == (fun y =>
       transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p^ # y))))
  := match p with idpath => fun _ => 1 end.


(** *** Functorial action *)

(** The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. *)
Definition functor_forall {A : Type} {P : A -> Type} {B : Type} {Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b)
  := (fun g b => f1 _ (g (f0 b))).

Definition ap_functor_forall `{Funext} {A : Type} {P : A -> Type} {B : Type} {Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
    (g g' : forall a:A, P a) (h : g == g')
  : ap (functor_forall f0 f1) (path_forall _ _ h)
    = path_forall _ _ (fun b:B => (ap (f1 b) (h (f0 b)))). 
Proof.
  revert h.  equiv_intro (@apD10 A P g g') h.
  destruct h.  simpl.
  path_via (idpath (functor_forall f0 f1 g)).
  exact (ap (ap (functor_forall f0 f1)) (path_forall_1 g)).
  symmetry.  apply path_forall_1.
Defined.

(** *** Equivalences *)


(** *** Truncatedness: any dependent product of n-types is an n-type *)

Instance Contr_forall `{Funext}
  {A : Type} {P : A -> Type} `{forall a, Contr (P a)}
  : Contr (forall a, P a).
Proof.
  exists (fun a => center (P a)).  
  intro f.  apply path_forall.  intro a.  apply contr.
Defined.

(** TODO: move to [Equivalences.v].
    TODO: define injectivity as a property of functions? *)
Definition equiv_inj {A B:Type} (e : A -> B) `{IsEquiv A B e} {x y : A}
  : (e x = e y) -> x = y
:= (fun (p : e x = e y) =>
  (eissect e x)^ @ ap (e ^-1) p @ eissect e y).

(** TODO: move. *)
Instance ap_equiv {A B} (e : A -> B) `{IsEquiv A B e} (x y:A)
  : IsEquiv (@ap _ _ e x y).
Proof.    
  apply isequiv_adjointify with (equiv_inj e).
  (* eisretr *)
  intro p.  unfold equiv_inj.
  path_via (ap e ((eissect e x) ^ @ ap e ^-1 p) @ ap e (eissect e y)).
    apply ap_pp.
  path_via ((ap e (eissect e x) ^ @ ap e (ap e ^-1 p)) @ ap e (eissect e y)).  
    apply (ap (fun q => q @ ap e (eissect e y))).  apply ap_pp.
  path_via (ap e (eissect e x) ^ @ (ap e (ap e ^-1 p) @ ap e (eissect e y))).  
  path_via (ap e (eissect e x) ^ @ ((eisretr e (e x)) @ p)).  apply ap.
    path_via (ap e (ap e ^-1 p) @ (eisretr e (e y))).  
      apply ap.  symmetry.  apply eisadj.
    path_via (ap (compose e (e ^-1)) p @ (eisretr e (e y))).  
      apply (ap (fun q => q @ (eisretr e (e y)))).
      symmetry.  apply (@ap_compose _ _ _ (e ^-1) e).
    path_via (eisretr e (e x) @ (ap (idmap) p)).
      apply (concat_Ap (eisretr e)).
    apply ap.  apply ap_idmap.
  path_via ((ap e (eissect e x) ^ @ eisretr e (e x)) @ p).
  path_via (1 @ p).
  apply (ap (fun q => q @ p)).
  path_via (ap e (eissect e x) ^ @ ap e (eissect e x)). 
    apply ap.  apply eisadj.
  path_via (ap e ((eissect e x) ^ @ eissect e x)).
    symmetry.  apply ap_pp. 
  change (idpath (e x)) with (ap e (idpath x)).  apply ap.  apply concat_Vp.
  (* eissect *)
  intro p.  destruct p.  unfold equiv_inj.  simpl.
  path_via ((eissect e x)^ @ eissect e x).
    apply (ap (fun p => p @ eissect e x)).  apply concat_p1. 
  apply concat_Vp.
Defined.

(** TODO: move. *)
Definition Trunc_resp_equiv {n} {A B} (e : A -> B) `{IsEquiv A B e}
  `{Trunc  n A}
  : Trunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [ | n' IH]; simpl in *.
  (* case [n = -2], i.e. contractibility *)
    intros A A_trunc B e e_is_eq.  apply Contr_equiv_contr.
  (* case n = trunc_S n' *)
    intros A A_trunc B e e_is_eq.
    equiv_intro e x.  equiv_intro e y.
    apply (IH (x = y) (A_trunc x y) (e x = e y) (ap e)). 
    apply ap_equiv; assumption.
Defined.

Instance Trunc_forall `{Funext}
  {A : Type} {P : A -> Type}
  {n : trunc_index} `{forall a, Trunc n (P a)}
  : Trunc n (forall a, P a).
Proof.
  generalize dependent P.  induction n as [ | n' IH].
  (* case [n = -2], i.e. contractibility *)
    simpl.  intros P P_contr.  apply Contr_forall.
  (* case n = trunc_S n' *)
  intros P P_trunc.   simpl.  intros f g.
  assert (Trunc n' (f == g)).
    apply IH.  intro a.  apply (P_trunc a).
  apply (Trunc_resp_equiv (apD10 ^-1)).
Defined.


(** *** Misc *)

(** Using the standard Haskell name for this, as it’s a handy utility function. 

Note: not sure if [P] will usually be deducible, or whether it would be better explicit. *)
Definition flip {A B : Type} {P : A -> B -> Type}
  : (forall a b, P a b) -> (forall b a, P a b)
:= fun f b a => f a b.

Instance isequiv_flip `{Funext} {A B : Type} {P : A -> B -> Type}
  : IsEquiv (@flip _ _ P).
Proof.
  set (flip_P := @flip _ _ P).
  set (flip_P_inv := @flip _ _ (flip P)).
  set (flip_P_is_sect := (fun f => 1) : Sect flip_P flip_P_inv).
  set (flip_P_is_retr := (fun g => 1) : Sect flip_P_inv flip_P).
  exists flip_P_inv flip_P_is_retr flip_P_is_sect.
  intro g.  exact 1.
Defined.
