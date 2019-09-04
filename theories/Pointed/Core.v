(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import Types.

Declare Scope pointed_scope.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Generalizable Variables A B f.

(** * Pointed Types *)

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A cartesian product of pointed types is pointed. *)
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(* Product of pTypes is a pType *)
Notation "X * Y" := (Build_pType (X * Y) ispointed_prod) : pointed_scope.

(** ** Pointed functions *)

(* A pointed map is a map with a proof that it preserves the point *)
Record pMap (A B : pType) :=
  { pointed_fun : A -> B ;
    point_eq : pointed_fun (point A) = point B }.

Arguments point_eq {A B} f : rename.
Coercion pointed_fun : pMap >-> Funclass.

Infix "->*" := pMap : pointed_scope.

Definition pmap_idmap {A : pType} : A ->* A
  := Build_pMap A A idmap 1.

Definition pmap_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: A ->* C
  := Build_pMap A C (g o f)
                (ap g (point_eq f) @ point_eq g).

Infix "o*" := pmap_compose : pointed_scope.

(** ** Pointed homotopies *)

(* A pointed homotopy is a homotopy with a proof that the presevation
   paths agree *)
Record pHomotopy {A B : pType} (f g : pMap A B) :=
  { pointed_htpy : f == g ;
    point_htpy : pointed_htpy (point A) @ point_eq g = point_eq f }.

Arguments Build_pHomotopy {A B f g} p q : rename.
Arguments point_htpy {A B f g} p : rename.
Arguments pointed_htpy {A B f g} p x.

Coercion pointed_htpy : pHomotopy >-> pointwise_paths.

Infix "==*" := pHomotopy : pointed_scope.

(** ** Pointed equivalences *)

(* A pointed equivalence is a pointed map and a proof that it is
  an equivalence *)
Record pEquiv (A B : pType) :=
  { pointed_equiv_fun : A ->* B ;
    pointed_isequiv : IsEquiv pointed_equiv_fun
  }.

(* TODO:
  It might be better behaved to define pEquiv as an equivalence and a proof that
  this equivalence is pointed.
    In pEquiv.v we have another constructor Build_pEquiv' which coq can
  infer faster than Build_pEquiv.
  *)

Infix "<~>*" := pEquiv : pointed_scope.

Coercion pointed_equiv_fun : pEquiv >-> pMap.
Global Existing Instance pointed_isequiv.

Coercion pointed_equiv_equiv {A B} (f : A <~>* B)
  : A <~> B := BuildEquiv A B f _.

(* Pointed type family *)
Definition pFam (A : pType) := {P : A -> Type & P (point A)}.

(* IsTrunc for a pointed type family *)
Definition IsTrunc_pFam n {A} (X : pFam A) := forall x, IsTrunc n (X.1 x).

(* Pointed sigma *)
Definition psigma : {A : pType & pFam A} -> pType.
Proof.
  intros [[A a] [P p]].
  exists {x : A & P x}.
  exact (a; p).
Defined.

(* Pointed pi types, note that the domain is not pointed *)
Definition pforall : {A : Type & A -> pType} -> pType.
Proof.
  intros [A F].
  exact (Build_pType (forall (a : A), pointed_type (F a)) (ispointed_type o F)).
Defined.

(** The following tactic often allows us to "pretend" that pointed maps and homotopies preserve basepoints strictly.  We have carefully defined [pMap] and [pHomotopy] so that when destructed, their second components are paths with right endpoints free, to which we can apply Paulin-Morhing path-induction. *)
Ltac pointed_reduce :=
  unfold pointed_fun, pointed_htpy; cbn;
  repeat match goal with
           | [ X : pType |- _ ] => destruct X as [X ?]
           | [ phi : pMap ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ alpha : pHomotopy ?f ?g |- _ ] => destruct alpha as [alpha ?]
           | [ equiv : pEquiv ?X ?Y |- _ ] => destruct equiv as [equiv ?]
         end;
  cbn in *; unfold point in *;
  path_induction; cbn;
  (** TODO: [pointed_reduce] uses [rewrite], and thus according to our current general rules, it should only be used in opaque proofs.  We don't yet need any of the proofs that use it to be transparent, but there's a good chance we will eventually.  At that point we can consider whether to allow it in transparent proofs, modify it to not use [rewrite], or exclude it from proofs that need to be transparent. *)
  rewrite ?concat_p1, ?concat_1p.

(** ** Equivalences *)

Definition issig_ptype : { X : Type & X } <~> pType.
Proof.
  issig Build_pType pointed_type ispointed_type.
Defined.

Definition issig_pmap (A B : pType)
: { f : A -> B & f (point A) = point B } <~> (A ->* B).
Proof.
  issig (@Build_pMap A B) (@pointed_fun A B) (@point_eq A B).
Defined.