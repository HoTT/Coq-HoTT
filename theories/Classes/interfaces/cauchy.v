From HoTT.Classes Require Import
     interfaces.abstract_algebra
     interfaces.rationals
     interfaces.orders
     implementations.peano_naturals
     theory.rationals.

Section cauchy.
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
  Context {Aabs : Abs F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  Section sequence.
    Context (x : nat -> F).

    Section modulus.
      Class CauchyModulus :=
        { cauchy_modulus : Qpos Q -> nat
        ; cauchy_convergence : forall epsilon : Qpos Q, forall m n,
              cauchy_modulus epsilon <= m -> cauchy_modulus epsilon <= n ->
              abs ((x m) - (x n)) < ' ((' epsilon) : Q)
        }.

    End modulus.

    Section limit.
      (* Context `{M : CauchyModulus}. *)

      Class IsLimit (l : F) := is_limit
        : forall epsilon : Qpos Q, hexists (fun N : nat => forall n : nat, N <= n -> abs (x n - l) < ' (' epsilon)).

    End limit.

  End sequence.

  Section complete.

    Class IsComplete := is_complete
      : forall x : nat -> F, forall M : CauchyModulus x, exists l, IsLimit x l.

  End complete.

End cauchy.
