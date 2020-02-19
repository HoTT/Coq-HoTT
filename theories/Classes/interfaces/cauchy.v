From HoTT.Classes Require Import
     interfaces.abstract_algebra
     interfaces.rationals
     interfaces.orders
     implementations.peano_naturals
     orders.semirings
     theory.rings
     theory.rationals.

Section cauchy.
  Generalizable Variables Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field.
  Generalizable Variables Fap Fplus Fmult Fzero Fone Fneg Frecip Fle Flt Fjoin Fmeet.
  Context (Q : Type).
  Context `{Qrats : @Rationals Q Qap Qplus Qmult Qzero Qone Qneg Qrecip Qle Qlt Qrats_to_field}.
  Context {Q_dec_paths : DecidablePaths Q}.
  Context {Qtriv : @TrivialApart Q Qap}.
  Context (F : Type).
  Context `{Forderedfield : @OrderedField F Flt Fle Fap Fzero Fone Fplus Fneg Fmult Fap Fzero Frecip Fjoin Fmeet}.
  Context {Fabs : Abs F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  Section sequence.
    Context (x : nat -> F).

    Section modulus.
      Class CauchyModulus (M : Qpos Q -> nat) :=
        cauchy_convergence : forall epsilon : Qpos Q, forall m n,
              M epsilon <= m -> M epsilon <= n ->
              abs ((x m) - (x n)) < ' ((' epsilon) : Q).

    End modulus.

    Section limit.
      (* Context `{M : CauchyModulus}. *)

      Class IsLimit (l : F) := is_limit
        : forall epsilon : Qpos Q, hexists (fun N : nat => forall n : nat, N <= n -> abs (x n - l) < ' (' epsilon)).

    End limit.

    Section modulus_close.

      Generalizable Variable M.

      Context `{CauchyModulus M}.

      Axiom modulus_close_limit : forall {l}
                                         (islim : IsLimit l)
                                         (epsilon : Qpos Q),
          x (M (( epsilon) / 2)) - ' (' epsilon)
        < l
        < x (M (( epsilon) / 2)) + ' (' epsilon).

    End modulus_close.

  End sequence.

  Section complete.

    Class IsComplete := is_complete
      : forall x : nat -> F, forall M , CauchyModulus x M -> exists l, IsLimit x l.

  End complete.

End cauchy.
