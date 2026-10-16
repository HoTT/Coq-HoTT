(** * Instantiating the analysis results *)

(** The results of [Analysis/] are stated for an abstract model [Q] of the rationals and an abstract Archimedean, Cauchy complete ordered field [F].  We build their hypotheses for the integers as pairs of natural numbers, the rationals as fractions of these integers and the Dedekind reals over these rationals, and check that besides [Funext] and [Univalence] only the postulates of the library's higher inductive types (truncations and quotients) are assumed.  We pass the instances explicitly, since instance search is slow on these concrete types. *)

From HoTT Require Import Basics Spaces.Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.integers
  interfaces.rationals
  interfaces.round
  interfaces.archimedean
  interfaces.cauchy
  implementations.peano_naturals
  implementations.natpair_integers
  implementations.field_of_fractions
  implementations.integer_fractions
  theory.nat_distance
  theory.rationals
  orders.orders.
From HoTT.Analysis Require Import
  DedekindReals.

Import NatPair.Instances.
Import (hints) Frac FracField.

(** The models. *)
Notation Zm := (NatPair.Z nat).
Notation Qm := (FracField.F Zm).
Notation Rm := (DedekindReals Qm).

(** The instantiation is concrete, so we use global universes. *)
Local Unset Universe Polymorphism.

Section models.
  Context `{Funext} `{Univalence}.

  Definition rationals_Qm := rationals_fracfield Zm (Zdom:=NatPair.Z_integral_domain nat).
  Definition trivialapart_Qm := trivialapart_fracfield Zm.
  Definition decidablepaths_Qm : DecidablePaths Qm := FracField.F_dec (H1:=NatPair.Z_integral_domain nat).
  Definition roundupstrict_Qm := roundupstrict_fracfield Zm (Zdom:=NatPair.Z_integral_domain nat).
  Definition trichotomy_Qm : Trichotomy (A:=Qm) (<)
    := lt_trichotomy (H:=pseudoorder_fracfield Zm (Zdom:=NatPair.Z_integral_domain nat))
         (TrivialApart0:=trivialapart_Qm) (H0:=decidablepaths_Qm).

  (** The enumerations of the rationals and of pairs of a rational and a positive rational. *)
  Definition equiv_nat_Qm := equiv_nat_fracfield Zm (Zdom:=NatPair.Z_integral_domain nat).
  Definition equiv_nat_Qm_qpos
    := equiv_nat_rationals_qpos (Qrats:=rationals_Qm) (Qdec:=decidablepaths_Qm)
         (Qtrivialapart:=trivialapart_Qm) equiv_nat_Qm.

  (** The Dedekind reals are an Archimedean, Cauchy complete ordered field. *)
  Definition orderedfield_Rm
    := orderedfield_dedekindreals Qm (Qrats:=rationals_Qm) (Qdec:=decidablepaths_Qm)
         (Qtriv:=trivialapart_Qm) (Qroundup:=roundupstrict_Qm).
  Definition archimedean_Rm : @ArchimedeanProperty Qm _ Rm _ _ _ _ _ _ _ _ _ _ _ orderedfield_Rm _
    := archimedean_dedekindreals Qm (Qrats:=rationals_Qm) (Qdec:=decidablepaths_Qm)
         (Qtriv:=trivialapart_Qm) (Qroundup:=roundupstrict_Qm).
  Definition iscomplete_Rm
    : IsComplete Qm Rm (Forderedfield:=orderedfield_Rm)
    := iscomplete_dedekindreals Qm (Qrats:=rationals_Qm) (Qdec:=decidablepaths_Qm)
         (Qtriv:=trivialapart_Qm) (Qroundup:=roundupstrict_Qm).

End models.

(** Each hypothesis of the analysis results holds in the concrete models. *)
Check rationals_Qm.
Check trivialapart_Qm.
Check decidablepaths_Qm.
Check roundupstrict_Qm.
Check equiv_nat_Qm.
Check equiv_nat_Qm_qpos.
Check orderedfield_Rm.
Check archimedean_Rm.
Check iscomplete_Rm.
Print Assumptions equiv_nat_Qm_qpos.
Print Assumptions archimedean_Rm.
Print Assumptions iscomplete_Rm.

(** TODO: apply [exact_ivt], [approximate_ivt_locator], [banach_fixed_point], [merely_locator_iff_signed_digits] and [locator_limit] to these hypotheses. Elaborating the application either fails, because the universe of the existential in [ArchimedeanProperty] fixed by [archimedean_dedekindreals] differs from the one the results expect, or does not finish when the definitions are made universe polymorphic. *)
