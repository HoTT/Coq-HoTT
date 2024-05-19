From HoTT Require Import Basics.
From HoTT Require Import Algebra.Rings.Matrix.
From HoTT Require Import Spaces.Nat.Core Spaces.List.Core.
From HoTT Require Import Algebra.Rings.Z Spaces.BinInt.Core Algebra.Rings.CRing.
From HoTT Require Import Classes.interfaces.canonical_names.

Local Open Scope mc_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** Matrices can be built with lists of lists. *)
Definition test1 := Build_Matrix' nat 5 7
   [ [  1 ,  2 ,  3 ,  4 ,  5 ,  6 ,  7 ]
   , [  8 ,  9 , 10 , 11 , 12 , 13 , 14 ]
   , [ 15 , 16 , 17 , 18 , 19 , 20 , 21 ]
   , [ 22 , 23 , 24 , 25 , 26 , 27 , 28 ]
   , [ 29 , 30 , 31 , 32 , 33 , 34 , 35 ] ]
   ltac:(decide)
   ltac:(decide).

(** Malformed matrices are not accepted. *)
Fail Definition test2 := Build_Matrix' nat 2 2
   [ [ 1 , 2 ]
   , [ 3 , 4 , 5] ]
   ltac:(decide)
   ltac:(decide).

(** Matrices can also be built with functions. *)
Definition test2_A := Build_Matrix nat 4 4 (fun i j _ _ => i * j).

Definition test2_B := Build_Matrix' nat 4 4
   [ [  0 ,  0 ,  0 ,  0 ]
   , [  0 ,  1 ,  2 ,  3 ]
   , [  0 ,  2 ,  4 ,  6 ]
   , [  0 ,  3 ,  6 ,  9 ] ]
   ltac:(decide)
   ltac:(decide).

Definition test2 : entries test2_A = entries test2_B := idpath.

Local Open Scope binint_scope.

(** Matrices with ring entries can be multiplied *)

(** This is the first matrix. *)
Definition test3_A := Build_Matrix' cring_Z 3 2
   [ [ 1 ,  3 ]
   , [ 2 , -1 ]
   , [ 1 ,  1 ] ]
   ltac:(decide)
   ltac:(decide).

(** This is the second matrix. *)
Definition test3_B := Build_Matrix' cring_Z 2 4
   [ [  4 , 1 , 0 , -2 ]
   , [ -1 , 1 , 5 ,  1 ] ]
   ltac:(decide)
   ltac:(decide).

(** This is the expected result of the multiplication. *)
Definition test3_AB := Build_Matrix' cring_Z 3 4
   [ [  1 , 4 , 15 ,  1 ]
   , [  9 , 1 , -5 , -5 ]
   , [  3 , 2 ,  5 , -1 ] ]
   ltac:(decide)
   ltac:(decide).

(** The entries should be the same, although the well-formedness proofs may differ definitionally. *)
Definition test3 : entries (matrix_mult test3_A test3_B) = entries test3_AB := idpath.

(** Here we check the minors of a matrix are computed correctly. *)

Definition test4 := Build_Matrix' cring_Z 3 3
   [ [  1 ,  3 ,  5 ]
   , [  2 ,  4 ,  6 ]
   , [  7 ,  8 ,  9 ] ]
   ltac:(decide)
   ltac:(decide).

Definition test4_minor_0_1 := Build_Matrix' cring_Z 2 2
   [ [  2 ,  6 ]
   , [  7 ,  9 ] ]
   ltac:(decide)
   ltac:(decide).

Definition test4_minor_0_1_eq
   : entries (matrix_minor 0 1 test4) = entries test4_minor_0_1
   := idpath.

Definition test4_minor_1_1 := Build_Matrix' cring_Z 2 2
   [ [  1 ,  5 ]
   , [  7 ,  9 ] ]
   ltac:(decide)
   ltac:(decide).

Definition test4_minor_1_1_eq
   : entries (matrix_minor 1 1 test4) = entries test4_minor_1_1
   := idpath.

