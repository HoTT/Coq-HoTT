From HoTT.Basics Require Import Overture.

Inductive imported_marker_carrier : Type := imported_marker_value.
Class ImportedMarker := imported_marker : imported_marker_carrier.
#[export] Instance imported_marker_instance : ImportedMarker := imported_marker_value.
