Require Import Basics.
Require Import Diagrams.Diagram.
Require Import Diagrams.Graph.
Require Import Diagrams.Cone.
Require Import Diagrams.ConstantDiagram.

Local Open Scope path_scope.
Generalizable All Variables.

(** This file contains the definition of limits, and functoriality results on limits. *)

(** * Limits *)

(** A Limit is the extremity of a cone. *)

Class IsLimit `(D : Diagram G) (Q : Type) := {
  islimit_cone :: Cone Q D;
  islimit_unicone : UniversalCone islimit_cone;
}.
Coercion islimit_cone : IsLimit >-> Cone.

Arguments Build_IsLimit {G D Q} C H : rename.
Arguments islimit_cone {G D Q} C : rename.
Arguments islimit_unicone {G D Q} H : rename.

(** [cone_precompose_inv] is defined for convenience: it is only the inverse of [cone_precompose]. It allows to recover the map [h] from a cone [C']. *)

Definition cone_precompose_inv `{D: Diagram G} {Q X}
  (H : IsLimit D Q) (C' : Cone X D) : X -> Q
  := @equiv_inv _ _ _ (islimit_unicone H X) C'.


(** * Existence of limits *)

Record Limit `(D : Diagram G) := {
  lim : forall i, D i;
  limp : forall i j (g : G i j), D _f g (lim i) = lim j;
}.

Arguments lim {_ _}.
Arguments limp {_ _}.

Definition cone_limit `(D : Diagram G) : Cone (Limit D) D.
Proof.
  srapply Build_Cone.
  + intros i x.
    exact (lim x i).
  + intros i j g x.
    apply limp.
Defined.

Instance unicone_limit `(D : Diagram G)
  : UniversalCone (cone_limit D).
Proof.
  srapply Build_UniversalCone; intro Y.
  srapply isequiv_adjointify.
  { intros c y.
    srapply Build_Limit.
    { intro i.
      exact (legs c i y). }
    intros i j g.
    apply legs_comm. }
  all: intro; reflexivity.
Defined.

Instance islimit_limit `(D : Diagram G) : IsLimit D (Limit D)
  := Build_IsLimit (cone_limit _) _.

(** * Functoriality of limits *)

Section FunctorialityLimit.

  Context `{Funext} {G : Graph}.

  (** Limits are preserved by composition with a (diagram) equivalence. *)

  Definition islimit_precompose_equiv {D : Diagram G} `(f : Q <~> Q')
    : IsLimit D Q' -> IsLimit D Q.
  Proof.
    intros HQ.
    srapply (Build_IsLimit (cone_precompose HQ f) _).
    apply cone_precompose_equiv_universality, HQ.
  Defined.

  Definition islimit_postcompose_equiv {D1 D2 : Diagram G} (m : D1 ~d~ D2)
    {Q : Type} : IsLimit D1 Q -> IsLimit D2 Q.
  Proof.
    intros HQ.
    srapply (Build_IsLimit (cone_postcompose m HQ) _).
    apply cone_postcompose_equiv_universality, HQ.
  Defined.

  (** A diagram map [m] : [D1] => [D2] induces a map between any two limits of [D1] and [D2]. *)

  Definition functor_limit {D1 D2 : Diagram G} (m : DiagramMap D1 D2)
    {Q1 Q2} (HQ1 : IsLimit D1 Q1) (HQ2 : IsLimit D2 Q2)
    : Q1 -> Q2 := cone_precompose_inv HQ2 (cone_postcompose m HQ1).

  (** And this map commutes with diagram map. *)

  Definition functor_limit_commute {D1 D2 : Diagram G}
    (m : DiagramMap D1 D2) {Q1 Q2}
    (HQ1 : IsLimit D1 Q1) (HQ2 : IsLimit D2 Q2)
    : cone_postcompose m HQ1
      = cone_precompose HQ2 (functor_limit m HQ1 HQ2)
    := (eisretr (cone_precompose HQ2) _)^.

  (** ** Limits of equivalent diagrams *)

  (** Now we have than two equivalent diagrams have equivalent limits. *)

  Context {D1 D2 : Diagram G} (m : D1 ~d~ D2) {Q1 Q2}
    (HQ1 : IsLimit D1 Q1) (HQ2 : IsLimit D2 Q2).

  Definition functor_limit_eissect
    : functor_limit m HQ1 HQ2
      o functor_limit (diagram_equiv_inv m) HQ2 HQ1 == idmap.
  Proof.
    apply ap10.
    srapply (equiv_inj (cone_precompose HQ2) _).
    1: apply HQ2.
    etransitivity.
    2:symmetry; apply cone_precompose_identity.
    etransitivity.
    1: apply cone_precompose_comp.
    rewrite eisretr, cone_postcompose_precompose, eisretr.
    rewrite cone_postcompose_comp, diagram_inv_is_section.
    apply cone_postcompose_identity.
  Defined.

  Definition functor_limit_eisretr
    : functor_limit (diagram_equiv_inv m) HQ2 HQ1
      o functor_limit m HQ1 HQ2 == idmap.
  Proof.
    apply ap10.
    srapply (equiv_inj (cone_precompose HQ1) _).
    1: apply HQ1.
    etransitivity.
    2:symmetry; apply cone_precompose_identity.
    etransitivity.
    1: apply cone_precompose_comp.
    rewrite eisretr, cone_postcompose_precompose, eisretr.
    rewrite cone_postcompose_comp, diagram_inv_is_retraction.
    apply cone_postcompose_identity.
  Defined.

  #[export] Instance isequiv_functor_limit
    : IsEquiv (functor_limit m HQ1 HQ2)
    := isequiv_adjointify _ _
      functor_limit_eissect functor_limit_eisretr.

  Definition equiv_functor_limit : Q1 <~> Q2
    := Build_Equiv _ _ _ isequiv_functor_limit.

End FunctorialityLimit.

(** * Unicity of limits *)

(** A particular case of the functoriality result is that all limits of a diagram are equivalent (and hence equal in presence of univalence). *)

Theorem limit_unicity `{Funext} {G : Graph} {D : Diagram G} {Q1 Q2 : Type}
  (HQ1 : IsLimit D Q1) (HQ2 : IsLimit D Q2)
  : Q1 <~> Q2.
Proof.
  srapply equiv_functor_limit.
  srapply (Build_diagram_equiv (diagram_idmap D)).
Defined.

(** * Limits are right adjoint to constant diagram *)

Theorem limit_adjoint {G : Graph} {D : Diagram G} {C : Type}
  : (C -> Limit D) <~> DiagramMap (diagram_const C) D.
Proof.
  srapply equiv_adjointify.
  { intro f.
    srapply Build_DiagramMap.
    { intros i c.
      apply lim, f, c. }
    intros i j g x.
    apply limp. }
  { intros [f p] c.
    srapply Build_Limit.
    { intro i.
      apply f, c. }
    intros i j g.
    apply p. }
  1,2: intro; reflexivity.
Defined.

