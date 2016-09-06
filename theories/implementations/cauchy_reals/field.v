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
  HoTTClasses.implementations.cauchy_completion.

Require Export
  HoTTClasses.implementations.cauchy_reals.base
  HoTTClasses.implementations.cauchy_reals.abs
  HoTTClasses.implementations.cauchy_reals.order
  HoTTClasses.implementations.cauchy_reals.metric
  HoTTClasses.implementations.cauchy_reals.ring
  HoTTClasses.implementations.cauchy_reals.full_order
  HoTTClasses.implementations.cauchy_reals.full_ring
  HoTTClasses.implementations.cauchy_reals.recip.

Local Set Universe Minimization ToSet.

Global Instance real_field : Field real.
Proof.
split;try apply _.
apply R_recip_inverse.
Qed.
