(* -*- mode: coq; mode: visual-line -*- *)

Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import UnivalenceImpliesFunext.
Require Import HIT.Truncations HIT.Suspension.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope pointed_scope.

(** * Coinductive Spectra *)

(** ** Definitions *)

CoInductive IsSpectrum : pType -> Type :=
  | isspectrum_loops : forall E, IsSpectrum E -> IsSpectrum (loops E).

Existing Class IsSpectrum.

Definition Spectrum := { E : pType & IsSpectrum E }.

Definition loops_oo : Spectrum -> pType := pr1.
Global Instance isspectrum_loops_oo (E : Spectrum)
: IsSpectrum (loops_oo E)
  := pr2 E.

(** *** Loop spectra *)

Global Existing Instance isspectrum_loops.

Definition loopsp : Spectrum -> Spectrum.
Proof.
  intros [E ?].
  exists (loops E).
  exact _.
Defined.

(** *** Coinductive frobnication *)

(** This doesn't seem to be necessary at the moment. *)
Definition frobsp {E : pType} (Es : IsSpectrum E)
: IsSpectrum E.
Proof.
  destruct Es.
  exact (isspectrum_loops E Es).
Defined.

Definition frobsp_eq {E : pType} (Es : IsSpectrum E)
: Es = frobsp Es.
Proof.
  destruct Es.
  reflexivity.
Defined.

(** ** The inverse of loops *)

Definition unloopsp : Spectrum -> Spectrum.
Proof.
  intros [E Es].
  destruct Es.
  exact (E;Es).
Defined.

(** Intriguingly, we can define this equivalence even though in general, path-spaces of coinductive types are ill-specified. *)
Definition equiv_loopsp : Spectrum <~> Spectrum.
Proof.
  refine (equiv_adjointify loopsp unloopsp _ _).
  - intros E. destruct E as [E Es]. destruct Es.
    reflexivity.
  - intros E. destruct E as [E Es]. destruct Es.
    reflexivity.
Defined.

(** ** Maps of spectra *)

CoInductive IsSpMap
: forall (E F : pType) (f : E ->* F)
         (Es : IsSpectrum E) (Fs : IsSpectrum F), Type :=
| spmap_loop : forall E F f Es Fs,
                 IsSpMap E F f Es Fs ->
                 IsSpMap (loops E) (loops F) (loops_functor f) _ _.

Arguments IsSpMap {E F} f {_ _}.
Existing Class IsSpMap.

Definition SpMap (E F : Spectrum)
  := { f : loops_oo E ->* loops_oo F & IsSpMap f }.

(** *** Functoriality of loop spectra *)

Definition loops_oo_functor {E F : Spectrum}
: SpMap E F -> (loops_oo E ->* loops_oo F)
  := pr1.
Global Instance isspmap_loops_oo_functor {E F} (f : SpMap E F)
: IsSpMap (loops_oo_functor f)
  := pr2 f.

CoFixpoint isspmap_loops_functor
           {E F : pType} {Es : IsSpectrum E} {Fs : IsSpectrum F}
           (f : E ->* F) {fs : IsSpMap f}
: IsSpMap (loops_functor f).
Proof.
  destruct fs.
  refine (spmap_loop (loops E) (loops F) (loops_functor f) _ _ _).
Qed.

Global Existing Instance isspmap_loops_functor.

Definition loopsp_functor {E F} (f : SpMap E F)
: SpMap (loopsp E) (loopsp F).
Proof.
  destruct f as [f ?].
  exists (loops_functor f).
  exact _.
Defined.

(** ** Truncation *)

(** TODO: Generalize this to all integers *)
CoFixpoint isspectrum_tr `{Univalence} (n : trunc_index)
           {A : pType} (As : IsSpectrum A)
: IsSpectrum (pTr n A).
Proof.
  destruct As.
  assert (s : IsSpectrum (loops (pTr n.+1 E))).
  { apply isspectrum_loops. by apply isspectrum_tr. }
  exact (transport IsSpectrum (ptr_loops_eq n E)^ s).
Defined.

Global Existing Instance isspectrum_tr.

Definition Trsp `{Univalence} (n : trunc_index)
: Spectrum -> Spectrum.
Proof.
  intros [E ?].
  exists (pTr n E).
  exact _.
Defined.

(** ** Suspension *)



(** ** Fibers *)
