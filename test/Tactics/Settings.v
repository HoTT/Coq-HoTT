From HoTT.Basics Require Import Overture.
From HoTT_Tests.Tactics Require SettingsImportedHints.

(** Requiring a module must not activate its exported instances. *)
Goal SettingsImportedHints.ImportedMarker.
Proof.
  Fail typeclasses eauto.
  exact SettingsImportedHints.imported_marker_instance.
Qed.

(** Importing the same module must activate them. *)
Import SettingsImportedHints.
Goal ImportedMarker.
Proof.
  typeclasses eauto.
Qed.

(** Parameters are omitted in asymmetric constructor patterns. *)
Inductive settings_box (A : Type) := settings_box_in : A -> settings_box A.
Definition settings_unbox {A} (b : settings_box A) : A :=
  match b with settings_box_in a => a end.
Goal settings_unbox (settings_box_in nat O) = O.
Proof.
  reflexivity.
Qed.

(** Explicit constructor patterns also handle implicit non-parameter fields. *)
Inductive settings_packed := settings_pack : forall A : Type, A -> settings_packed.
Arguments settings_pack {A} _.
Definition settings_unpack (b : settings_packed) : Type :=
  match b with @settings_pack A a => A end.
Goal settings_unpack (settings_pack O) = nat.
Proof.
  reflexivity.
Qed.
