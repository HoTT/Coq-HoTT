From HoTT Require Import Basics TruncType ExcludedMiddle abstract_algebra.


(** * Cardinals *)

(* The cardinal of a type is its set truncation and cardinals are compared by injections. *)

Definition Cardinal := Trunc 0 HSet.
Definition card A `{IsHSet A} : Cardinal
  := tr (Build_HSet A).


Global Instance le_cardinal `{Univalence} : Le Cardinal
  := fun A B => Trunc_rec (fun A : HSet =>
             Trunc_rec (fun B : HSet =>
             (hexists (fun f : A -> B => IsInjective f)))
             B)
             A.

Global Instance is_mere_relation_le_cardinal `{Univalence}
  : is_mere_relation Cardinal (<=).
Proof.
  rapply Trunc_ind; intros A.
  rapply Trunc_ind; intros B.
  exact _.
Qed.

Lemma isinjective_Compose {A B C} (f : B -> C) (g : A -> B) :
  IsInjective f ->
  IsInjective g ->
  IsInjective (f ∘ g).
Proof.
  intros injective_f injective_g.
  intros x y eq. apply injective_g, injective_f. assumption.
Qed.

Global Instance transitive_le_Cardinal `{Univalence}
  : Transitive (le : Le Cardinal).
Proof.
  unfold Transitive.
  rapply Trunc_ind; intros X.
  rapply Trunc_ind; intros Y.
  rapply Trunc_ind; intros Z.
  rapply Trunc_rec; intros [f injective_f].
  rapply Trunc_rec; intros [g injective_g].
  apply tr. exists (g ∘ f).
  apply isinjective_Compose; assumption.
Qed.



(** * Cardinality comparisons *)

(* We also work with cardinality comparisons directly to avoid unnecessary type truncations via cardinals. *)

Definition inject X Y :=
  { f : X -> Y | IsInjective f }.

Lemma inject_refl X :
  inject X X.
Proof.
  exists (fun x => x). intros x x'. easy.
Qed.

Lemma inject_trans X Y Z :
  inject X Y -> inject Y Z -> inject X Z.
Proof.
  intros [f Hf] [g Hg]. exists (fun x => g (f x)).
  now apply isinjective_Compose.
Qed.

Definition hinject X Y :=
  hexists (@IsInjective X Y).

Lemma hinject_trans X Y Z :
  hinject X Y -> hinject Y Z -> hinject X Z.
Proof.
  intros H1 H2.
  eapply merely_destruct; try apply H1. intros [f Hf].
  eapply merely_destruct; try apply H2. intros [g Hg].
  apply tr. exists (fun x => g (f x)). now apply isinjective_Compose.
Qed.



(** * Infinity *)

(* We call a set infinite if nat embeds into it. *)

Definition infinite X :=
  inject nat X.
