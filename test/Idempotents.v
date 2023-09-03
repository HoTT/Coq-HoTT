From HoTT Require Import Idempotents.

(** Note that [Idempotent X], unlike [RetractOf X], lives in the same universe as [X], even if we demand that it contain the identity. *)
Check (fun (X:Type@{i}) => (idem_idmap X : (Idempotent X : Type@{i}))).

(** By contrast, [RetractOf X] does not live in the same universe as [X] if it is required to contain the identity retraction. *)
Fail Check (fun (X:Type@{i}) => (idmap_retractof X : (RetractOf X : Type@{i}))).

