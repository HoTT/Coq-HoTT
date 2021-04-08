(** * Tactic for proving laws about adjoint composition *)
Require Import HoTT.Categories.Category.Core HoTT.Categories.Functor.Core HoTT.Categories.NaturalTransformation.Core.
Require Import HoTT.Categories.Functor.Composition.Core.
Require Import HoTT.Categories.Functor.Composition.Laws.
Require Import HoTT.Categories.Adjoint.UnitCounit HoTT.Categories.Adjoint.Paths.
Require Import HoTT.Basics.PathGroupoids HoTT.Tactics HoTT.Types.Prod HoTT.Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Ltac law_t :=
  rewrite !transport_path_prod'; simpl;
  path_adjunction; simpl;
  repeat match goal with
           | [ |- context[unit (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @unit _ _ _ _) z)
           | [ |- context[counit (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @counit _ _ _ _) z)
           | [ |- context[components_of (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @components_of _ _ _ _) z)
         end;
  rewrite !transport_forall_constant;
  repeat
    match goal with
      | [ |- context[transport (fun y : Functor ?C ?D => ?f (y _0 ?x)%object)] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (y' x)) (@object_of C D))
      | [ |- context[transport (fun y : Functor ?C ?D => ?f (?g (y _0 ?x)%object))] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (y' x))) (@object_of C D))
      | [ |- context[transport (fun y : Functor ?C ?D => ?f (?g (?h (?i (y _0 ?x)%object))))] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (h (i (y' x))))) (@object_of C D))
      | [ |- context[transport (fun y : Functor ?C ?D => ?f (y _0 ?x)%object ?z)] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (y' x) z) (@object_of C D))
      | [ |- context[transport (fun y : Functor ?C ?D => ?f (?g (y _0 ?x)%object) ?z)] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (y' x)) z) (@object_of C D))
      | [ |- context[transport (fun y : Functor ?C ?D => ?f (?g (?h (?i (y _0 ?x)%object))) ?z)] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (h (i (y' x)))) z) (@object_of C D))
    end;
  unfold symmetry, symmetric_paths;
  rewrite ?ap_V;
  rewrite ?left_identity_fst, ?right_identity_fst, ?associativity_fst;
  simpl;
  repeat (
      rewrite
        ?identity_of,
      ?composition_of,
      ?Category.Core.left_identity,
      ?Category.Core.right_identity,
      ?Category.Core.associativity
    );
  try reflexivity.
