From HoTT Require Import ExcludedMiddle canonical_names.
From HoTT Require Import HIT.unique_choice.
From HoTT Require Import Spaces.Card.

From HoTT.Sets Require Import Ordinals.

Local Open Scope hprop_scope.

(** * Set-theoretic formulation of the axiom of choice (AC) *)

Monomorphic Axiom Choice : Type0.
Existing Class Choice.

Definition Choice_type :=
  forall (X Y : HSet) (R : X -> Y -> HProp), (forall x, hexists (R x)) -> hexists (fun f => forall x, R x (f x)).

Axiom AC : forall `{Choice}, Choice_type.

Global Instance is_global_axiom_propresizing : IsGlobalAxiom Choice := {}.



(** * The well-ordering theorem implies AC *)

Lemma WO_AC {LEM : ExcludedMiddle} :
  (forall (X : HSet), hexists (fun (A : Ordinal) => InjectsInto X A)) -> Choice_type.
Proof.
  intros H X Y R HR. specialize (H Y).
  eapply merely_destruct; try apply H.
  intros [A HA]. eapply merely_destruct; try apply HA.
  intros [f Hf]. apply tr. unshelve eexists.
  - intros x. assert (HR' : hexists (fun y => merely (R x y * forall y', R x y' -> f y < f y' \/ f y = f y'))).
    + pose proof (HAR := ordinal_has_minimal_hsolutions A (fun a => Build_HProp (merely (exists y, f y = a /\ R x y)))).
      eapply merely_destruct; try apply HAR.
      * eapply merely_destruct; try apply (HR x). intros [y Hy].
        apply tr. exists (f y). apply tr. exists y. by split.
      * intros [a [H1 H2]]. eapply merely_destruct; try apply H1.
        intros [y [<- Hy]]. apply tr. exists y. apply tr. split; trivial.
        intros y' Hy'. apply H2. apply tr. exists y'. split; trivial.
    + edestruct (@iota Y) as [y Hy]; try exact y. 2: split; try apply HR'. 1: exact _.
      intros y y' Hy Hy'.
      eapply merely_destruct; try apply Hy. intros [H1 H2].
      eapply merely_destruct; try apply Hy'. intros [H3 H4]. apply Hf.
      eapply merely_destruct; try apply (H2 y'); trivial. intros [H5|H5]; trivial.
      eapply merely_destruct; try apply (H4 y); trivial. intros [H6| -> ]; trivial.
      apply Empty_rec. apply (irreflexive_ordinal_relation _ _ _ (f y)).
      apply (ordinal_transitivity _ (f y')); trivial.
  - intros x. cbn. destruct iota as [y Hy]. eapply merely_destruct; try apply Hy. by intros [].
Qed.
