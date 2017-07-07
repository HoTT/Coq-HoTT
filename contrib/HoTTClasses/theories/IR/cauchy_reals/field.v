Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric
  HoTTClasses.IR.cauchy_completion.

Require Export
  HoTTClasses.IR.cauchy_reals.base
  HoTTClasses.IR.cauchy_reals.abs
  HoTTClasses.IR.cauchy_reals.order
  HoTTClasses.IR.cauchy_reals.metric
  HoTTClasses.IR.cauchy_reals.ring
  HoTTClasses.IR.cauchy_reals.full_order
  HoTTClasses.IR.cauchy_reals.full_ring
  HoTTClasses.IR.cauchy_reals.recip.

Local Set Universe Minimization ToSet.

Global Instance real_field : Field real.
Proof.
split;try apply _.
apply R_recip_inverse.
Qed.
