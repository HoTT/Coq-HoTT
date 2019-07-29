Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pEquiv.
Require Import Pointed.Loops.
Require Import HIT.Truncations.
Import TrM.


Local Open Scope pointed_scope.

(** ** Truncations *)

Global Instance ispointed_tr (n : trunc_index) (A : Type) `{IsPointed A}
: IsPointed (Tr n A)
  := tr (point A).

Definition pTr (n : trunc_index) (A : pType) : pType
  := Build_pType (Tr n A) _.

Definition pTr_functor {X Y : pType} (n : trunc_index) (f : X ->* Y)
: pTr n X ->* pTr n Y.
Proof.
  refine (Build_pMap (pTr n X) (pTr n Y) (Trunc_functor n f) _).
  exact (ap (@tr n Y) (point_eq f)).
Defined.

Definition pTr_pequiv {X Y : pType} (n : trunc_index) (f : X <~>* Y)
: pTr n X <~>* pTr n Y
  := Build_pEquiv _ _ (pTr_functor n f) _.

Definition ptr_loops `{Univalence} (n : trunc_index) (A : pType)
: pTr n (loops A) <~>* loops (pTr n.+1 A).
Proof.
  simple refine (issig_pequiv _ _ (_;_)).
  - apply equiv_path_Tr.
  - reflexivity.
Defined.

Definition ptr_loops_eq `{Univalence} (n : trunc_index) (A : pType)
: pTr n (loops A) = loops (pTr n.+1 A) :> pType
  := path_ptype (ptr_loops n A).
