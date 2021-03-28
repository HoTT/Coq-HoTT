Require Import Basics.Overture Basics.Decimal Basics.Hexadecimal.

(** * Decimal or Hexadecimal numbers *)

Variant uint := UIntDec (u:Decimal.uint) | UIntHex (u:Hexadecimal.uint).

Variant int := IntDec (i:Decimal.int) | IntHex (i:Hexadecimal.int).

Variant numeral := Dec (d:Decimal.decimal) | Hex (h:Hexadecimal.hexadecimal).

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register numeral as num.numeral.type.
Register numeral as num.number.type.

(** Pseudo-conversion functions used when declaring
    Numeral Notations on [uint] and [int]. *)

Definition uint_of_uint (i:uint) := i.
Definition int_of_int (i:int) := i.

(* Parsing / printing of decimal numbers *)
Number Notation uint uint_of_uint uint_of_uint : dec_uint_scope.
Number Notation int int_of_int int_of_int : dec_int_scope.
