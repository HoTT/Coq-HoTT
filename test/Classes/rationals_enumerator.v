From HoTT Require Import
  Basics
  Truncations.Core
  Spaces.Nat.Enumeration
  Classes.interfaces.abstract_algebra
  Classes.interfaces.rationals
  Classes.interfaces.orders
  Classes.theory.rationals.

(** Enumerating pairs of a rational and a positive rational: the surjectivity is found by instance search. *)
Section test.
  Context `{Funext} `{Univalence}.
  Context {Q : Type} {Qap : Apart Q}
    {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt Q}
    {QtoField : RationalsToField Q}
    {Qrats : Rationals Q}
    {Qtrivialapart : TrivialApart Q} {Qdec : DecidablePaths Q}.

  Definition test_enumerable `{Enumerable Q}
    : IsSurjection (nat_prod_enumerator (enumerator Q) Qpos_enumerator)
    := _.

  (** Starting from a bare surjection, we pass it as the [Enumerable Q] instance. *)
  Definition test_surjection (e : nat -> Q) `{IsSurjection e}
    : IsSurjection (nat_prod_enumerator e (Qpos_enumerator (Qenum:=Build_Enumerable Q e _)))
    := _.
End test.
