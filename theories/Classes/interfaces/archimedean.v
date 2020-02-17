From HoTT.Classes Require Import
     interfaces.abstract_algebra
     interfaces.rationals
     interfaces.orders.

Section property.
  Generalizable Variables Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field.
  Generalizable Variables Fap Fplus Fmult Fzero Fone Fneg Frecip Fle Flt Fjoin Fmeet.
  Context (Q : Type).
  Context `{Qrats : @Rationals Q Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field}.
  Context (F : Type).
  Context `{Aorderedfield : @OrderedField F Flt Fle Fap Fzero Fone Fplus Fneg Fmult Fap Fzero Frecip Fjoin Fmeet}.
  (* We are assuming `A` to be of characteristic 0 because this is
  what `rationals_to_field` requires. But this requirement should
  eventually simply be implemented by the fact that F is an ordered
  field. *)
  Context {Achar : FieldCharacteristic F 0}.

  Class ArchimedeanProperty := archimedean_property
    : forall x y, x < y -> hexists (fun q => x < (rationals_to_field Q F q) < y).

End property.
