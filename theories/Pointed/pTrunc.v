Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Pointed.pEquiv.
Require Import Pointed.Loops.
Require Import HoTT.Truncations.
Import TrM.

Local Open Scope pointed_scope.

(** ** Truncations *)

Global Instance ispointed_tr (n : trunc_index) (A : Type) `{IsPointed A}
  : IsPointed (Tr n A) := tr (point A).

Definition pTr (n : trunc_index) (A : pType) : pType
  := Build_pType (Tr n A) _.

Definition ptr_functor {X Y : pType} (n : trunc_index) (f : X ->* Y)
  : pTr n X ->* pTr n Y := Build_pMap (pTr n X) (pTr n Y)
    (Trunc_functor n f) (ap (@tr n Y) (point_eq f)).

Definition ptr_functor_pmap_idmap {X : pType} n
  : ptr_functor n (@pmap_idmap X) ==* pmap_idmap.
Proof.
  serapply Build_pHomotopy.
  { intro x.
    by strip_truncations. }
  reflexivity.
Defined.

Definition ptr_functor_pmap_compose n {X Y Z : pType} (f : X ->* Y) (g : Y ->* Z)
  : ptr_functor n (g o* f) ==* ptr_functor n g o* ptr_functor n f.
Proof.
  serapply Build_pHomotopy.
  { intro x.
    by strip_truncations. }
  by pointed_reduce.
Defined.

Definition ptr_pequiv {X Y : pType} (n : trunc_index) (f : X <~>* Y)
  : pTr n X <~>* pTr n Y := Build_pEquiv _ _ (ptr_functor n f) _.

Definition ptr_loops `{Univalence} (n : trunc_index) (A : pType)
  : pTr n (loops A) <~>* loops (pTr n.+1 A).
Proof.
  serapply Build_pEquiv'.
  1: apply equiv_path_Tr.
  reflexivity.
Defined.

Definition ptr_loops_eq `{Univalence} (n : trunc_index) (A : pType)
  : pTr n (loops A) = loops (pTr n.+1 A) :> pType
  := path_ptype (ptr_loops n A).

Definition pequiv_ptr_functor {X Y : pType} n
  : X <~>* Y -> pTr n X <~>* pTr n Y.
Proof.
  intro e.
  serapply Build_pEquiv.
  { apply ptr_functor, e. }
  exact _.
Defined.

