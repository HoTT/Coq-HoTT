From HoTT Require Import Basics Spaces.Int Spaces.SInt.

(** Test the conversion functions between [Int] and [SInt]. *)
Definition test1 : int_to_sint zero = sint_zero := idpath.

Definition test2 : int_to_sint (int_pred2 zero) = sint_NegS 0 := idpath.

Definition test2' : int_to_sint (int_pred zero) = sint_NegS 0 := idpath.

Definition test3 : int_to_sint (int_succ (int_pred2 zero)) = sint_zero := idpath.

Definition test4 : int_to_sint (int_neg (int_succ (int_succ zero))) = sint_NegS 1 := idpath.

Definition test5 : int_to_sint (-4)%int = sint_NegS 3 := idpath.

Definition test6 : int_to_sint ((0.+1)%int) = sint_PosS 0 := idpath.

Definition test7 : int_to_sint ((0.+1)-1)%int = sint_zero := idpath.

Definition test8 : sint_to_int sint_zero = zero := idpath.

Definition test9 : sint_to_int (sint_PosS 0) = int_succ zero := idpath.

Definition test10 : sint_to_int (sint_NegS 0) = int_pred zero := idpath.

(** Test the reduction function for [Int]. *)
Definition test11 : int_reduce (int_succ (int_pred (int_succ zero))) = int_succ zero := idpath.

Definition test12 : int_reduce (int_pred2 zero) = int_pred zero := idpath.

Definition test13 : int_reduce (int_pred (int_succ (int_pred2 zero))) = int_pred zero := idpath.

(** Arithmetic does not generally produce a term in normal form, so [3 - 2] is not definitionally [1].  Reducing first makes the two sides agree. *)
Definition test14 : int_reduce (3 - 2)%int = 1%int := idpath.

(** Since [Int] has decidable equality, such facts can also be proved automatically. *)
Definition test15 : (3 - 2)%int = 1%int := ltac:(decide).
