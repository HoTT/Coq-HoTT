(* -*- mode: coq; mode: visual-line -*- *)

(** * Spectra *)

Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Tactics.
Require Import Pointed.
Require Import HoTT.Truncations.

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

Definition strunc `{Univalence} (k : trunc_index) (E : Spectrum) : Spectrum.
Proof.
  simple refine (Build_Spectrum (Build_Prespectrum (fun n => pTr (trunc_index_inc n k) (E n)) _) _).
  - intros n.
    exact ((ptr_loops _ (E n.+1)) o*E (ptr_pequiv _ (equiv_glue E n))).
  - intros n. unfold glue.
    serapply isequiv_compose.
Defined.
