(** Because we do not use the Coq standard library at all, we have
    to start from scratch. *)

Require Export Notations.
Require Export Logic.
Require Export Datatypes.
Require Export Coq.Init.Tactics.
Require Export Specif.
Require Coq.Init.Decimal.
Require Coq.Init.Hexadecimal.
Require Coq.Init.Numeral.
Require Coq.Init.Number.
Require Coq.Init.Nat.

Declare ML Module "number_string_notation_plugin".

(* Parsing / printing of decimal numbers *)
Arguments Nat.of_uint d%dec_uint_scope.
Arguments Nat.of_int d%dec_int_scope.
Number Notation Number.uint Number.uint_of_uint Number.uint_of_uint
  : dec_uint_scope.
Number Notation Number.int Number.int_of_int Number.int_of_int
  : dec_int_scope.

(* Parsing / printing of [nat] numbers *)
Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5001) : nat_scope.

Add Search Blacklist "_admitted" "_subproof" "Private_".
