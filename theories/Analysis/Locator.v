Require Import
        HoTT.Basics
        HoTT.BoundedSearch
        HoTT.Types.Universe
        HoTT.Types.Sum
        HoTT.Spaces.Finite
        HoTT.ExcludedMiddle
        HoTT.Todo.

Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.interfaces.orders
        HoTT.Classes.interfaces.integers
        HoTT.Classes.interfaces.rationals
        HoTT.Classes.interfaces.cauchy
        HoTT.Classes.theory.rationals.

Section locator.
  Generalizable Variables Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field.
  Generalizable Variables Fap Fplus Fmult Fzero Fone Fneg Frecip Fle Flt Fjoin Fmeet.
  Context (Q : Type).
  Context `{Qrats : @Rationals Q Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field}.
  Context (F : Type).
  Context `{Forderedfield : @OrderedField F Flt Fle Fap Fzero Fone Fplus Fneg Fmult Fap Fzero Frecip Fjoin Fmeet}.
  (* We are assuming `F` to be of characteristic 0 because this is
  what `rationals_to_field` requires. But this requirement should
  eventually simply be implemented by the fact that F is an ordered
  field. *)
  Context {Fchar : FieldCharacteristic F 0}.
  Context {Fabs : Abs F}.
  Context {Fcomplete : IsComplete Q F}.

  Context `{Funext} `{Univalence}.

  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  (* Definition of a locator for a fixed real number. *)
  Definition locator (x : F) := forall q r : Q, q < r -> (' q < x) + (x < ' r).

  Section classical.
    Context `{ExcludedMiddle}.

    Lemma all_reals_locators (x : F) : locator x.
    Proof.
      intros q r ltqr.
      case (LEM (' q < x)).
      - refine _.
      - exact inl.
      - todo (~ ' q < x -> (' q < x) + (x < ' r)).
    Admitted.

  End classical.

End locator.
