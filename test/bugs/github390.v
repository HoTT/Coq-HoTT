From HoTT Require Import Basics Pointed Homotopy.Suspension.

(** Check that [ispointed_susp] doesn't require just a [Set] *)
Check (fun A : Type => _ : IsPointed (Susp A)).
Check (@ispointed_susp Type).
Check (@ispointed_susp Set).

