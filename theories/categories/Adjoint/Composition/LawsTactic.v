(** * Tactic for proving laws about adjoint composition *)
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core.
Require Import Functor.Composition.Laws.
Require Import Adjoint.UnitCounit Adjoint.Paths.
Require Import PathGroupoids HoTT.Tactics types.Prod types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Ltac law_t :=
  rewrite !transport_path_prod'; simpl;
  path_adjunction; simpl;
  repeat match goal with
           | [ |- appcontext[unit (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @unit _ _ _ _) z)
           | [ |- appcontext[counit (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @counit _ _ _ _) z)
           | [ |- appcontext[components_of (transport ?P ?p ?z)] ]
             => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => @components_of _ _ _ _) z)
         end;
  rewrite !transport_forall_constant;
  repeat
    match goal with
      | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x))] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (y' x)) (@object_of C D))
      | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x)))] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (y' x))) (@object_of C D))
      | [ |- appcontext[transport (fun y => ?f (?g (?h (?i (@object_of ?C ?D y ?x)))))] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (h (i (y' x))))) (@object_of C D))
      | [ |- appcontext[transport (fun y => ?f (@object_of ?C ?D y ?x) ?z)] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (y' x) z) (@object_of C D))
      | [ |- appcontext[transport (fun y => ?f (?g (@object_of ?C ?D y ?x)) ?z)] ]
        => rewrite (fun a b => @transport_compose _ _ a b (fun y' => f (g (y' x)) z) (@object_of C D))
      | [ |- appcontext[transport (fun y => ?f (?g (?h (?i (@object_of ?C ?D y ?x)))) ?z)] ]
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
