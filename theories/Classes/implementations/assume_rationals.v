Require Import
     HoTT.Classes.interfaces.canonical_names
     HoTT.Classes.interfaces.orders
     HoTT.Classes.interfaces.rationals
     HoTT.Classes.theory.rationals.

Monomorphic Universe UQ.
Parameters (Q : Type@{UQ}) (Qap : Apart@{UQ UQ} Q)
  (Qplus : Plus Q) (Qmult : Mult Q)
  (Qzero : Zero Q) (Qone : One Q) (Qneg : Negate Q) (Qrecip : DecRecip Q)
  (Qle : Le@{UQ UQ} Q) (Qlt : Lt@{UQ UQ} Q)
  (QtoField : RationalsToField@{UQ UQ UQ UQ} Q)
  (Qrats : Rationals@{UQ UQ UQ UQ UQ UQ UQ UQ} Q)
  (Qtrivialapart : TrivialApart Q) (Qdec : DecidablePaths Q)
  (Qmeet : Meet Q) (Qjoin : Join Q) (Qlattice : LatticeOrder Qle)
  (Qle_total : TotalRelation (@le Q _))
  (Qabs : Abs Q).
(* I don't even want to know why this is necessary. *)
Parameter Qenum : Enumerable Q.
Notation "Q+" := (Qpos Q).

Existing Instances Qap Qplus Qmult Qzero Qone Qneg Qrecip
         Qle Qlt QtoField Qrats Qtrivialapart Qdec
         Qmeet Qjoin Qlattice Qle_total Qabs Qenum.
