From HoTT Require Import Basics Basics.Numerals.Decimal Spaces.SInt.

(** This tests a former bug in the parsing function.  But it couldn't be triggered, because the parser doesn't let you type "-0" for some reason. *)
Definition test1 : sint_of_number_int (IntDec (Neg Decimal.zero)) = sint_zero := idpath.
