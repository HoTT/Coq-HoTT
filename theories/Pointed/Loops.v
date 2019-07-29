Require Import Basics.
Require Import Types.
Require Import Fibrations.
Require Import Factorization.
Require Import HIT.Truncations.
Require Import HIT.Connectedness.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pEquiv.
Require Import Pointed.pHomotopy.

Import TrM.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** ** Loop spaces *)

(** The type [x = x] is pointed. *)
Global Instance ispointed_loops A (a : A)
: IsPointed (a = a)
  := idpath.

Definition loops (A : pType) : pType
  := Build_pType (point A = point A) _.

Fixpoint iterated_loops (n : nat) (A : pType) : pType
  := match n with
       | O => A
       | S p => loops (iterated_loops p A)
     end.

(* Inner unfolding for iterated loops *)
Lemma unfold_iterated_loops (n : nat) (X : pType)
  : iterated_loops n.+1 X = iterated_loops n (loops X).
Proof.
  induction n.
  1: reflexivity.
  change (iterated_loops n.+2 X)
    with (loops (iterated_loops n.+1 X)).
  by refine (ap loops IHn @ _).
Defined.

(** The loop space decreases the truncation level by one.  We don't bother making this an instance because it is automatically found by typeclass search, but we record it here in case anyone is looking for it. *)
Definition istrunc_loops {n} (A : pType) `{IsTrunc n.+1 A}
  : IsTrunc n (loops A) := _.

(** Similarly for connectedness. *)
Definition isconnected_loops `{Univalence} {n} (A : pType) `{IsConnected n.+1 A}
  : IsConnected n (loops A) := _.

(** ** Functoriality of loop spaces *)

Definition loops_functor {A B : pType} (f : A ->* B)
: (loops A) ->* (loops B).
Proof.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  apply moveR_Vp; simpl.
  refine (concat_1p _ @ (concat_p1 _)^).
Defined.

Fixpoint iterated_loops_functor {A B : pType} (n : nat) 
  : (A ->* B) -> (iterated_loops n A) ->* (iterated_loops n B).
Proof.
  destruct n.
  1: exact idmap.
  refine (loops_functor o _).
  apply iterated_loops_functor.
Defined.

(* Loops functor respects composition *)
Definition loops_functor_compose {A B C : pType} (g : B ->* C) (f : A ->* B)
  : (loops_functor (pmap_compose g f))
  ==* (pmap_compose (loops_functor g) (loops_functor f)).
Proof.
  serapply Build_pHomotopy.
  { intros p.
    pointed_reduce.
    apply ap_compose. }
  by pointed_reduce.
Qed.

(* Loops functor respects identity *)
Definition loops_functor_idmap (A : pType)
  : loops_functor (pmap_idmap A) ==* pmap_idmap (loops A).
Proof.
  serapply Build_pHomotopy.
  { intro p.
    refine (concat_1p _ @ concat_p1 _ @ ap_idmap _). }
  reflexivity.
Defined.

(* Loops functor distributes over concatenation *)
Lemma loops_functor_pp {X Y : pType} (f : pMap X Y) (x y : loops X)
  : loops_functor f (x @ y) = loops_functor f x @ loops_functor f y.
Proof.
  pointed_reduce.
  apply ap_pp.
Qed.

Definition loops_2functor {A B : pType} {f g : A ->* B} (p : f ==* g)
  : (loops_functor f) ==* (loops_functor g).
Proof.
  pointed_reduce.
  serapply Build_pHomotopy; cbn.
  { intro q.
    refine (_ @ (concat_p1 _)^ @ (concat_1p _)^).
    apply moveR_Vp, concat_Ap. }
  hott_simpl.
Qed.

(** ** Loop spaces and truncation and connectedness *)

(** The loop space functor decreases the truncation level by one.  *)
Global Instance istrunc_loops_functor {n} (A B : pType) (f : A ->* B)
  `{IsTruncMap n.+1 _ _ f} : IsTruncMap n (loops_functor f).
Proof.
  intro p.
  refine (trunc_equiv' _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_Vp _ _ _))).
  refine (trunc_equiv' _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_pM _ _ _))).
Defined.

(** And likewise the connectedness.  *)
Global Instance isconnected_loops_functor `{Univalence} {n : trunc_index}
       (A B : pType) (f : A ->* B) `{IsConnMap n.+1 _ _ f}
: IsConnMap n (loops_functor f).
Proof.
  intro p; cbn.
  refine (isconnected_equiv' n _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_Vp _ _ _)) _).
  refine (isconnected_equiv' n _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_pM _ _ _)) _).
  refine (isconnected_equiv' n _ (hfiber_ap _)^-1 _).
Defined.

(** It follows that loop spaces "commute with images". *)
Definition equiv_loops_image `{Univalence} n {A B : pType} (f : A ->* B)
  : loops (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))
  <~> image n (loops_functor f).
Proof.
  set (C := (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))).
  pose (g := Build_pMap A C (factor1 (image n.+1 f)) 1).
  pose (h := Build_pMap C B (factor2 (image n.+1 f)) (point_eq f)).
  transparent assert (I : (Factorization
    (@IsConnMap n) (@MapIn n) (loops_functor f))).
  { refine (@Build_Factorization (@IsConnMap n) (@MapIn n)
      (loops A) (loops B) (loops_functor f) (loops C)
      (loops_functor g) (loops_functor h) _ _ _).
    intros x; symmetry.
    refine (_ @ pointed_htpy (loops_functor_compose h g) x).
    simpl.
    abstract (rewrite !concat_1p; reflexivity). }
  exact (path_intermediate (path_factor (O_factsys n) (loops_functor f) I
    (image n (loops_functor f)))).
Defined.

(** ** Loop spaces *)

(** Loop inversion is a pointed equivalence *)
Definition loops_inv (A : pType) : loops A <~>* loops A.
Proof.
  serapply Build_pEquiv.
  1: exact (Build_pMap (loops A) (loops A) inverse 1).
  apply isequiv_path_inverse.
Defined.

Definition phomotopy_ap `{Funext} {A B C D: pType} (f g : A ->* B)
  (h : (A ->* B) -> (C ->* D))
  : f ==* g -> h f ==* h g.
Proof.
  intro p.
  by destruct (path_pmap p).
Defined.

(* Loops functor preserves equivalences *)
Definition loops_functor_equiv `{Funext} (A B : pType)
  : A <~>* B -> loops A <~>* loops B.
Proof.
  intro f.
  serapply pequiv_adjointify.
  1: apply loops_functor, f.
  1: apply loops_functor, (pequiv_inverse f).
  1,2: refine ((loops_functor_compose _ _)^* @* _ @* loops_functor_idmap _).
  1,2: apply phomotopy_ap.
  1: apply peisretr.
  apply peissect.
Defined.

(* Loops preserves products *)
Lemma loops_prod `{Univalence} (X Y : pType)
  : loops (X * Y) <~>* loops X * loops Y.
Proof.
  serapply Build_pEquiv.
  + serapply Build_pMap.
    - intro p.
      by refine ((equiv_path_prod (point _) (point (X * Y)))^-1%equiv _).
    - reflexivity.
  + exact _.
Defined.

(* Iterated loops products preserve products *)
Lemma iterated_loops_prod `{Univalence} (X Y : pType) {n}
  : iterated_loops n (X * Y) <~>* (iterated_loops n X) * (iterated_loops n Y).
Proof.
  induction n.
  + reflexivity.
  + refine (pequiv_compose _ (loops_prod _ _)).
    by apply loops_functor_equiv.
Defined.

