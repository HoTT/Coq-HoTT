From HoTT Require Import Colimits.Quotient.

(** This eases with reading the checks. *)
Set Printing Universes.
Unset Printing Notations.

(** Enforcing universe constraints on Quotient types *)

(** Quotient types have 3 universe variables:
  - The type to be quotiented, [A]
  - The equivalence relation, [R]
  - The universe the quotient type lives in, think of as a max of the other 2 *)
Check Quotient@{i j k}.
Check class_of@{i j k}.
Check qglue@{i j k}.

(** TODO: these are less general than it should be. *)
Check Quotient_ind_hprop@{i j k}.
Check in_class@{i j k r}.
Check decidable_in_class@{u1 u2 u3 u4 u5}.
Check path_in_class_of@{i j k r _}.
Check related_quotient_paths@{i j k r}.

(** Universe levels of the quotient + the target type. *)
Check Quotient_ind@{i j k r}.
Check Quotient_rec@{i j k r}.
Check Quotient_ind_beta_qglue@{i j k r}.
Check Quotient_rec_beta_qglue@{i j k r}.
