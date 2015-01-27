(* -*- mode: coq; mode: visual-line -*- *)
(** * Pointed Types *)

Require Import Overture PathGroupoids Equivalences.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
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

(** ** Loop spaces *)

(** The type [x = x] is pointed. *)
Global Instance ispointed_loops A (a : A)
: IsPointed (a = a)
  := idpath.

(** We can build an iterated loop space *)
Definition loops (A : pType) : pType :=
  Build_pType (point A = point A) idpath.

Fixpoint iterated_loops (n : nat) (A : Type) `{H : IsPointed A}
         {struct n} : pType
  := match n with
       | O => Build_pType A (@point A H)
       | S p => iterated_loops p (point A = point A)
     end.

(** ** Pointed functions *)

Record pMap (A B : pType) :=
  { pointed_fun : A -> B ;
    point_eq : pointed_fun (point A) = point B }.

Arguments point_eq {A B} f : rename.
Coercion pointed_fun : pMap >-> Funclass.

Infix "->*" := pMap (at level 99) : pointed_scope.
Local Open Scope pointed_scope.

Definition loops_functor {A B : pType} (f : A ->* B)
: (loops A) ->* (loops B).
Proof.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  apply moveR_Vp; simpl.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Definition pmap_idmap (A : pType): A ->* A
  := Build_pMap A A idmap 1.

Definition pmap_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: A ->* C
  := Build_pMap A C (g o f)
                (ap g (point_eq f) @ point_eq g).

Infix "o*" := pmap_compose (at level 40) : pointed_scope.

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

Infix "==*" := pHomotopy (at level 70, no associativity) : pointed_scope.

(** The following tactic often allows us to "pretend" that pointed maps and homotopies preserve basepoints strictly.  We have carefully defined [pMap] and [pHomotopy] so that when destructed, their second components are paths with right endpoints free, to which we can apply Paulin-Morhing path-induction. *)
Ltac pointed_reduce :=
  unfold pointed_fun, pointed_htpy; cbn;
  repeat match goal with
           | [ X : pType |- _ ] => destruct X as [X ?]
           | [ phi : pMap ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ alpha : pHomotopy ?f ?g |- _ ] => destruct alpha as [alpha ?]
         end;
  cbn in *; unfold point in *;
  path_induction; cbn;
  (** TODO: [pointed_reduce] uses [rewrite], and thus according to our current general rules, it should only be used in opaque proofs.  We don't yet need any of the proofs that use it to be transparent, but there's a good chance we will eventually.  At that point we can consider whether to allow it in transparent proofs, modify it to not use [rewrite], or exclude it from proofs that need to be transparent. *)
  rewrite ?concat_p1, ?concat_1p.

Definition loops_2functor {A B : pType} {f g : A ->* B} (p : f ==* g)
: (loops_functor f) ==* (loops_functor g).
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); simpl.
  - intros q.
    refine (_ @ (concat_1p _)^).
    refine (_ @ (concat_p1 _)^).
    apply moveR_Vp.
    refine (concat_Ap p q).
  - simpl.
    abstract (rewrite !concat_p1; reflexivity).
Qed.

(** ** Associativity of pointed map composition *)

Definition pmap_compose_assoc {A B C D : pType}
           (h : C ->* D) (g : B ->* C) (f : A ->* B)
: (h o* g) o* f ==* h o* (g o* f).
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap A ==* f.
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap B o* f ==* f.
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
           (h : B ->* C) (p : f ==* g)
: h o* f ==* h o* g.
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros a; apply ap, p.
  - reflexivity.
Qed.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
           {g h : B ->* C} (p : g ==* h)
: g o* f ==* h o* f.
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros a; apply p.
  - refine (concat_p1 _ @ (concat_1p _)^).
Qed.

(** ** Composition of pointed homotopies *)

Definition phomotopy_compose {A B : pType} {f g h : A ->* B}
           (p : f ==* g) (q : g ==* h)
: f ==* h.
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros x; exact (p x @ q x).
  - apply concat_p1.
Qed.

Infix "@*" := phomotopy_compose (at level 30) : pointed_scope.

Definition phomotopy_inverse {A B : pType} {f g : A ->* B}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; pointed_reduce.
  refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - apply concat_Vp.
Qed.

Notation "p ^*" := (phomotopy_inverse p) (at level 20) : pointed_scope.

(** ** Functoriality of loop spaces *)

Definition loops_functor_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: (loops_functor (pmap_compose g f))
   ==* (pmap_compose (loops_functor g) (loops_functor f)).
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); simpl.
  - intros p.
    apply whiskerL, whiskerR.
    refine (_ @ ap (ap g) (concat_1p _)^).
    refine (_ @ ap (ap g) (concat_p1 _)^).
    apply ap_compose.
  - reflexivity.
Qed.

Definition loops_functor_idmap (A : pType)
: loops_functor (pmap_idmap A) ==* pmap_idmap (loops A).
Proof.
  pointed_reduce.
  refine (Build_pHomotopy _ _); simpl.
  - intros p.
    refine (concat_1p _ @ concat_p1 _ @ ap_idmap _).
  - reflexivity.
Qed.

(** ** Pointed equivalences *)

Record pEquiv (A B : pType) :=
  { pointed_equiv_fun : A ->* B ;
    pointed_isequiv : IsEquiv pointed_equiv_fun
  }.

Infix "<~>*" := pEquiv (at level 85) : pointed_scope.

Coercion pointed_equiv_fun : pEquiv >-> pMap.
Global Existing Instance pointed_isequiv.

Definition pointed_equiv_equiv {A B} (f : A <~>* B)
: A <~> B
  := BuildEquiv A B f _.

Coercion pointed_equiv_equiv : pEquiv >-> Equiv.

Definition pequiv_inverse {A B} (f : A <~>* B)
: B <~>* A.
Proof.
  refine (Build_pEquiv B A
            (Build_pMap _ _ f^-1 _)
            _).
  apply moveR_equiv_V; symmetry; apply point_eq.
Defined.
