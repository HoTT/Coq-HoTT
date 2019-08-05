(* -*- mode: coq; mode: visual-line -*- *)

(** * Spectra *)

Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Tactics.
Require Import Pointed.
Require Import HIT.Truncations.

Import TrM.

Local Open Scope nat_scope.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope pointed_scope.

(** ** Basic Definitions of Spectra *)

Record Prespectrum :=
  { deloop :> nat -> pType
    ; glue : forall n, deloop n ->* loops (deloop (n .+1)) }.

Class IsSpectrum (E : Prespectrum) :=
  is_equiv_glue : forall n, IsEquiv (glue E n).

Existing Instance is_equiv_glue.

Definition equiv_glue (E : Prespectrum) `{IsSpectrum E}
: forall n, E n <~>* loops (E n.+1)
  := fun n => Build_pEquiv _ _ (glue E n) _.

Record Spectrum :=
  { to_prespectrum :> Prespectrum
    ; to_is_spectrum : IsSpectrum to_prespectrum }.

Existing Instance to_is_spectrum.

(** ** Truncations of spectra *)

Definition strunc `{Univalence} (k : trunc_index) (E : Spectrum) : Spectrum
  := Build_Spectrum
      (Build_Prespectrum (fun n : nat => pTr (trunc_index_inc n k) (E n))
        (fun n : nat => ptr_loops (trunc_index_inc n k) (E n.+1)
          o*E ptr_pequiv (trunc_index_inc n k) (equiv_glue E n)))
      (fun n : nat => pointed_isequiv (pTr (trunc_index_inc n k) (E n))
        (loops (pTr (trunc_index_inc n k).+1 (E n.+1)))
        (ptr_loops (trunc_index_inc n k) (E n.+1)
          o*E ptr_pequiv (trunc_index_inc n k) (equiv_glue E n))).
