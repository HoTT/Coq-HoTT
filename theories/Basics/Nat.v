Require Import Basics.Overture Basics.Decimal Basics.Hexadecimal Basics.Numeral.

Notation "n .+1" := (S n) : nat_scope.
Notation "n .+2" := (n.+1.+1)%nat   : nat_scope.
Notation "n .+3" := (n.+1.+2)%nat   : nat_scope.
Notation "n .+4" := (n.+1.+3)%nat   : nat_scope.
Notation "n .+5" := (n.+1.+4)%nat   : nat_scope.


(** ** Tail-recursive versions of [add] and [mul] *)

Fixpoint tail_add n m :=
  match n with
    | O => m
    | S n => tail_add n (S m)
  end.

(** [tail_addmul r n m] is [r + n * m]. *)

Fixpoint tail_addmul r n m :=
  match n with
    | O => r
    | S n => tail_addmul (tail_add m r) n m
  end.

Definition tail_mul n m := tail_addmul O n m.

(** ** Conversion with a decimal representation for printing/parsing *)

Local Notation ten := (S (S (S (S (S (S (S (S (S (S O)))))))))).

Fixpoint of_uint_acc (d:Decimal.uint)(acc:nat) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 d => of_uint_acc d (tail_mul ten acc)
  | Decimal.D1 d => of_uint_acc d (S (tail_mul ten acc))
  | Decimal.D2 d => of_uint_acc d (S (S (tail_mul ten acc)))
  | Decimal.D3 d => of_uint_acc d (S (S (S (tail_mul ten acc))))
  | Decimal.D4 d => of_uint_acc d (S (S (S (S (tail_mul ten acc)))))
  | Decimal.D5 d => of_uint_acc d (S (S (S (S (S (tail_mul ten acc))))))
  | Decimal.D6 d => of_uint_acc d (S (S (S (S (S (S (tail_mul ten acc)))))))
  | Decimal.D7 d => of_uint_acc d (S (S (S (S (S (S (S (tail_mul ten acc))))))))
  | Decimal.D8 d => of_uint_acc d (S (S (S (S (S (S (S (S (tail_mul ten acc)))))))))
  | Decimal.D9 d => of_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul ten acc))))))))))
  end.

Definition of_uint (d:Decimal.uint) := of_uint_acc d O.

Local Notation sixteen := (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))).

Fixpoint of_hex_uint_acc (d:Hexadecimal.uint)(acc:nat) :=
  match d with
  | Hexadecimal.Nil => acc
  | Hexadecimal.D0 d => of_hex_uint_acc d (tail_mul sixteen acc)
  | Hexadecimal.D1 d => of_hex_uint_acc d (S (tail_mul sixteen acc))
  | Hexadecimal.D2 d => of_hex_uint_acc d (S (S (tail_mul sixteen acc)))
  | Hexadecimal.D3 d => of_hex_uint_acc d (S (S (S (tail_mul sixteen acc))))
  | Hexadecimal.D4 d => of_hex_uint_acc d (S (S (S (S (tail_mul sixteen acc)))))
  | Hexadecimal.D5 d => of_hex_uint_acc d (S (S (S (S (S (tail_mul sixteen acc))))))
  | Hexadecimal.D6 d => of_hex_uint_acc d (S (S (S (S (S (S (tail_mul sixteen acc)))))))
  | Hexadecimal.D7 d => of_hex_uint_acc d (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))
  | Hexadecimal.D8 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))
  | Hexadecimal.D9 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))
  | Hexadecimal.Da d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))
  | Hexadecimal.Db d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))
  | Hexadecimal.Dc d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))
  | Hexadecimal.Dd d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))))
  | Hexadecimal.De d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))))
  | Hexadecimal.Df d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))))))
  end.

Definition of_hex_uint (d:Hexadecimal.uint) := of_hex_uint_acc d O.

Definition of_num_uint (d:Numeral.uint) :=
  match d with
  | Numeral.UIntDec d => of_uint d
  | Numeral.UIntHex d => of_hex_uint d
  end.

Fixpoint to_little_uint n acc :=
  match n with
  | O => acc
  | S n => to_little_uint n (Decimal.Little.succ acc)
  end.

Definition to_uint n :=
  Decimal.rev (to_little_uint n Decimal.zero).

Definition to_num_uint n := Numeral.UIntDec (to_uint n).

Definition of_int (d:Decimal.int) : option nat :=
  match Decimal.norm d with
    | Decimal.Pos u => Some (of_uint u)
    | _ => None
  end.

Definition of_hex_int (d:Hexadecimal.int) : option nat :=
  match Hexadecimal.norm d with
    | Hexadecimal.Pos u => Some (of_hex_uint u)
    | _ => None
  end.

Definition of_num_int (d:Numeral.int) : option nat :=
  match d with
  | Numeral.IntDec d => of_int d
  | Numeral.IntHex d => of_hex_int d
  end.

Definition to_int n := Decimal.Pos (to_uint n).

Definition to_num_int n := Numeral.IntDec (to_int n).

Arguments of_uint d%dec_uint_scope.
Arguments of_int d%dec_int_scope.

(* Parsing / printing of [nat] numbers *)
Number Notation nat of_num_uint to_num_uint (abstract after 5001) : nat_scope.


