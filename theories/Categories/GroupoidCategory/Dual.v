(** * Propositional self-duality of groupoid categories *)
Require Import Category.Core GroupoidCategory.Core Category.Paths Category.Dual.
Require Import HoTT.Types HoTT.UnivalenceImpliesFunext.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

Lemma path_groupoid_dual `{Univalence} `{IsTrunc 1 X}
: (groupoid_category X)^op = groupoid_category X.
Proof.
  repeat match goal with
           | _ => intro
           | _ => progress cbn
           | _ => reflexivity
           | _ => apply path_forall
           | _ => apply (path_universe (symmetry _ _))
           | _ => exact (center _)
           | _ => progress rewrite ?transport_path_universe, ?transport_path_universe_V
           | _ => progress path_category
           | _ => progress path_induction
         end.
Qed.
