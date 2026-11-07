From HoTT Require Import Basics.Overture Basics.Classes Basics.Tactics.
From HoTT.Classes Require Import
  interfaces.canonical_names interfaces.abstract_algebra
  theory.groups theory.rings implementations.field_of_fractions.

Generalizable Variables R.

(** The cancellation lemmas need neither set truncation nor two-sided group laws. *)
Section OneSidedInverses.
  Local Open Scope mc_mult_scope.
  Context {A : Type} `{op : SgOp A} {e : A} {i : A -> A}
    `{!Associative op} (x y z : A).

  Section LeftUnit.
    Context `{!LeftIdentity op e}.

    Goal RightInverse op i e -> x * (i x * y) = y.
    Proof.
      intros ?.
      apply sgop_inv_g_Vg.
    Qed.

    Goal LeftInverse op i e -> i x * (x * y) = y.
    Proof.
      intros ?.
      apply sgop_inv_V_gg.
    Qed.
  End LeftUnit.

  Section RightUnit.
    Context `{!RightIdentity op e}.

    Goal LeftInverse op i e -> (x * i y) * y = x.
    Proof.
      intros ?.
      apply sgop_inv_gV_g.
    Qed.

    Goal RightInverse op i e -> (x * y) * i y = x.
    Proof.
      intros ?.
      apply sgop_inv_gg_V.
    Qed.

    Goal LeftInverse op i e -> (x * i y) * (y * i z) = x * i z.
    Proof.
      intros ?.
      apply inverse_telescope.
    Qed.
  End RightUnit.
End OneSidedInverses.

(** These instances also work on arbitrary types with the relevant laws. *)
Section GroupLaws.
  Local Open Scope mc_mult_scope.
  Context {A : Type} `{op : SgOp A} `{unit : MonUnit A}
    `{i : Inverse A} `{!Associative (.*.)}.

  Section LeftInverse.
    Context `{!LeftIdentity (.*.) mon_unit,
      !LeftInverse (.*.) (^) mon_unit}.

    Goal forall x : A, LeftCancellation (.*.) x.
    Proof.
      exact group_cancelL.
    Qed.

    Context `{!RightIdentity (.*.) mon_unit}.

    Goal Involutive (^).
    Proof.
      exact inverse_involutive.
    Qed.

    Goal IsInjective (^).
    Proof.
      exact isinj_group_inverse.
    Qed.

    Goal mon_unit^ = mon_unit.
    Proof.
      exact inverse_mon_unit.
    Qed.
  End LeftInverse.

  Section RightInverse.
    Context `{!RightIdentity (.*.) mon_unit,
      !RightInverse (.*.) (^) mon_unit}.

    Goal forall x : A, RightCancellation (.*.) x.
    Proof.
      exact group_cancelR.
    Qed.
  End RightInverse.
End GroupLaws.

Local Open Scope mc_scope.

(** Ordinary rewriting specializes [sg_op] and [inv] to ring operations. *)
Section Rings.
  Context `{IsRing R} (x y : R).

  Goal x + (-x + y) = y.
  Proof.
    rewrite sgop_inv_g_Vg.
    reflexivity.
  Qed.

  Goal -x + (x + y) = y.
  Proof.
    rewrite sgop_inv_V_gg.
    reflexivity.
  Qed.

  Goal (x - y) + y = x.
  Proof.
    rewrite sgop_inv_gV_g.
    reflexivity.
  Qed.

  Goal (x + y) - y = x.
  Proof.
    rewrite sgop_inv_gg_V.
    reflexivity.
  Qed.

  Goal -(x + y) = -y + -x.
  Proof.
    rewrite inverse_sg_op.
    reflexivity.
  Qed.
End Rings.

(** On the fraction field, unification must not produce a case analysis on the private quotient type. In particular, these proofs must pass [Qed], not just solve the goals. *)
Section Fractions.
  Import FracField.
  Context `{Funext} `{Univalence}
    `{IsIntegralDomain R} `{DecidablePaths R}.
  Context (x y z w : F R).

  Goal x + (-x + y) = y.
  Proof.
    rewrite sgop_inv_g_Vg.
    reflexivity.
  Qed.

  Goal -x + (x + y) = y.
  Proof.
    rewrite sgop_inv_V_gg.
    reflexivity.
  Qed.

  Goal (x - y) + y = x.
  Proof.
    rewrite sgop_inv_gV_g.
    reflexivity.
  Qed.

  Goal (x + y) - y = x.
  Proof.
    rewrite sgop_inv_gg_V.
    reflexivity.
  Qed.

  Goal -(x + y) = -y + -x.
  Proof.
    rewrite inverse_sg_op.
    reflexivity.
  Qed.

  Goal (x - y) + y = x.
  Proof.
    apply sgop_inv_gV_g.
  Qed.

  (** [rapply] uses full conversion, so pin the operations to avoid unfolding them while inferring [op] and [i]. *)
  Goal (x - y) + y = x.
  Proof.
    rapply (sgop_inv_gV_g (op := Fplus) (i := Fneg) x y).
  Qed.

  Goal (x + y) + (z + w) = (x + z) + (y + w).
  Proof.
    rewrite swap_middle.
    reflexivity.
  Qed.

  Goal (x * y) * (z * w) = (x * z) * (y * w).
  Proof.
    rewrite swap_middle.
    reflexivity.
  Qed.

  Goal (x - y) + (y - z) = x - z.
  Proof.
    rewrite inverse_telescope.
    reflexivity.
  Qed.

  Goal (z + x) - (z + y) = x - y.
  Proof.
    rewrite common_left_cancel.
    reflexivity.
  Qed.
End Fractions.
