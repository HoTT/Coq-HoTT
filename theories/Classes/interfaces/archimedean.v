From HoTT.Classes Require Import
     interfaces.abstract_algebra
     interfaces.rationals
     interfaces.orders.

Section property.
  Context (Q : Type).
  Context `{Qrats : Rationals Q}.
  Context (F : Type).
  Context `{Aorderedfield : OrderedField F}.
  (* We are assuming `A` to be of characteristic 0 because this is
  what `rationals_to_field` requires. But this requirement should
  eventually simply be implemented by the fact that F is an ordered
  field. *)
  Context {Achar : FieldCharacteristic F 0}.

  Definition qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  Class ArchimedeanProperty := archimedean_property
    : forall x y, x < y -> hexists (fun q => x < ' q < y).

End property.
