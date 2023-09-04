From HoTT Require Import Basics Types.

(** Check that nested sigma-type notation didn't get clobbered by surreal cuts *)
Check ({ l : Unit & { n : Unit & Unit }}).
