(** * Spectra *)

Require Import HoTT.Basics HoTT.Types.
Require Import Pointed.

Local Open Scope nat_scope.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope pointed_scope.

(** ** Basic Definitions of Spectra *)

Record Prespectrum :=
  { deloop :> nat -> pType
    ; glue : forall n, deloop n ->* loops (deloop (n .+1)) }.

Class IsSpectrum (E : Prespectrum) :=
  is_equiv_glue :: forall n, IsEquiv (glue E n).

Definition equiv_glue (E : Prespectrum) `{IsSpectrum E}
: forall n, E n <~>* loops (E n.+1)
  := fun n => Build_pEquiv _ _ (glue E n) _.

Record Spectrum :=
  { to_prespectrum :> Prespectrum
    ; to_is_spectrum :: IsSpectrum to_prespectrum }.

(** ** Truncations of spectra *)

Definition strunc `{Univalence} (k : trunc_index) (E : Spectrum) : Spectrum.
Proof.
  simple refine (Build_Spectrum (Build_Prespectrum (fun n => pTr (trunc_index_inc k n) (E n)) _) _).
  - intros n.
    exact ((ptr_loops _ (E n.+1)) o*E (pequiv_ptr_functor _ (equiv_glue E n))).
  - intros n. unfold glue.
    exact isequiv_compose.
Defined.
