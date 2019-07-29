(* -*- mode: coq; mode: visual-line -*- *)
(** * Pointed Types *)

Require Import Basics.
Require Import Types.
Local Open Scope path_scope.

Generalizable Variables A B f.

(** ** Constructions of pointed types *)

(** Any contractible type is pointed. *)
Global Instance ispointed_contr `{Contr A} : IsPointed A := center A.

(** A pi type with a pointed target is pointed. *)
Global Instance ispointed_forall `{H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a)
  := fun a => point (B a).

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A cartesian product of pointed types is pointed. *)
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(** ** Pointed functions *)

Record pMap (A B : pType) :=
  { pointed_fun : A -> B ;
    point_eq : pointed_fun (point A) = point B }.

Arguments point_eq {A B} f : rename.
Coercion pointed_fun : pMap >-> Funclass.

Declare Scope pointed_scope.

Infix "->*" := pMap : pointed_scope.

Local Open Scope pointed_scope.

Definition pmap_idmap (A : pType): A ->* A
  := Build_pMap A A idmap 1.

Definition pmap_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: A ->* C
  := Build_pMap A C (g o f)
                (ap g (point_eq f) @ point_eq g).

Infix "o*" := pmap_compose : pointed_scope.

(** Another option would be
<<
Delimit Scope pmap_scope with pmap.
Bind Scope pmap_scope with pMap.
Infix "o" := pmap_compose : pmap_scope.
>>
which would allow us to use [o] for pointed maps as well most of the time.  However, it would sometimes require adding [%pmap] scoping markers. *)

(** ** Pointed homotopies *)

Record pHomotopy {A B : pType} (f g : pMap A B) :=
  { pointed_htpy : f == g ;
    point_htpy : pointed_htpy (point A) @ point_eq g = point_eq f }.

Arguments Build_pHomotopy {A B f g} p q : rename.
Arguments point_htpy {A B f g} p : rename.
Arguments pointed_htpy {A B f g} p x.

Coercion pointed_htpy : pHomotopy >-> pointwise_paths.

Infix "==*" := pHomotopy : pointed_scope.

(** ** Pointed equivalences *)

Record pEquiv (A B : pType) :=
  { pointed_equiv_fun : A ->* B ;
    pointed_isequiv : IsEquiv pointed_equiv_fun
  }.

Infix "<~>*" := pEquiv : pointed_scope.

Coercion pointed_equiv_fun : pEquiv >-> pMap.
Global Existing Instance pointed_isequiv.

Definition pointed_equiv_equiv {A B} (f : A <~>* B)
: A <~> B
  := BuildEquiv A B f _.

Coercion pointed_equiv_equiv : pEquiv >-> Equiv.

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


Notation "X * Y" := (Build_pType (X * Y) ispointed_prod) : pointed_scope.
