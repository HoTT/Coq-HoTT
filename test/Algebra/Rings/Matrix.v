From HoTT Require Import Basics.
From HoTT Require Import Algebra.AbGroups.AbelianGroup.
From HoTT Require Import Algebra.Rings.Ring Algebra.Rings.Matrix.
From HoTT Require Import Spaces.Nat.Core Spaces.List.Core.
From HoTT Require Import Algebra.Rings.Z Spaces.Int Algebra.Rings.CRing.
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

Local Open Scope int_scope.

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

(** The entries are propositionally equal, but with our use of HIT integers they are not definitionally equal, since the same integer has many representations.  Applying [int_reduce] to each entry puts it into normal form, after which the two sides agree definitionally. Using [ltac:(decide)] also works, but is slower. *)
Definition test3
  : entries (matrix_map int_reduce (matrix_mult test3_A test3_B)) = entries test3_AB
  := idpath.

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

(** Squaring the exchange matrix gives the identity. *)
Definition test_exchange_matrix_square
  : entries (matrix_map int_reduce (matrix_mult
      (exchange_matrix cring_Z 3) (exchange_matrix cring_Z 3)))
    = entries (identity_matrix cring_Z 3)
  := idpath.

(** Exchange matrices reverse rows and columns of rectangular matrices. *)
Definition test_exchange_matrix_rows_expected := Build_Matrix' cring_Z 3 2
  [ [ 1 ,  1 ]
  , [ 2 , -1 ]
  , [ 1 ,  3 ] ]
  ltac:(decide)
  ltac:(decide).

Definition test_exchange_matrix_columns_expected := Build_Matrix' cring_Z 3 2
  [ [  3 , 1 ]
  , [ -1 , 2 ]
  , [  1 , 1 ] ]
  ltac:(decide)
  ltac:(decide).

Definition test_exchange_matrix_rows
  : entries (matrix_map int_reduce
      (matrix_mult (exchange_matrix cring_Z 3) test3_A))
    = entries test_exchange_matrix_rows_expected
  := idpath.

Definition test_exchange_matrix_columns
  : entries (matrix_map int_reduce
      (matrix_mult test3_A (exchange_matrix cring_Z 2)))
    = entries test_exchange_matrix_columns_expected
  := idpath.

Definition test_exchange_matrix_rows_entry
  := entry_matrix_mult_exchange_l (R:=cring_Z)
      test3_A 0 1 ltac:(decide) ltac:(decide).

Definition test_exchange_matrix_columns_entry
  := entry_matrix_mult_exchange_r (A:=cring_Z)
      test3_A 1 0 ltac:(decide) ltac:(decide).

(** Centrosymmetry works without funext, including in dimension zero. *)
Section Centrosymmetric.
  Context (R : Ring).

  Goal IsCentrosymmetric (identity_matrix R 0).
  Proof.
    exact _.
  Qed.

  Goal IsCentrosymmetric (identity_matrix R 1).
  Proof.
    exact _.
  Qed.

  Context (n : nat) (M N : Matrix R n n).
  Context `{!IsCentrosymmetric M} `{!IsCentrosymmetric N}.

  Goal IsCentrosymmetric (matrix_mult M N).
  Proof.
    exact _.
  Qed.

  (** Closure instances can be applied repeatedly. *)
  Goal IsCentrosymmetric (matrix_negate (matrix_negate M)).
  Proof.
    exact _.
  Qed.

  Goal IsCentrosymmetric (matrix_plus M (matrix_negate N)).
  Proof.
    exact _.
  Qed.

  Goal IsCentrosymmetric
    (matrix_transpose (matrix_negate (matrix_transpose M))).
  Proof.
    exact _.
  Qed.

  (** Changing to the opposite ring requires no additional instance. *)
  Goal IsCentrosymmetric (A:=rng_op R) M.
  Proof.
    exact _.
  Qed.

  Goal matrix_mult (exchange_matrix R n) M
    = matrix_mult M (exchange_matrix R n).
  Proof.
    exact (exchange_matrix_iscentrosymmetric M).
  Qed.

  Goal forall P : Matrix R 0 0,
    matrix_mult (exchange_matrix R 0) P
      = matrix_mult P (exchange_matrix R 0) -> IsCentrosymmetric P.
  Proof.
    intros P p.
    exact (iscentrosymmetric_exchange_matrix p).
  Qed.
End Centrosymmetric.

(** Transpose does not require any algebraic structure on the entries. *)
Section CentrosymmetricType.
  Context (A : Type) (n : nat) (M : Matrix A n n).
  Context `{!IsCentrosymmetric M}.

  Goal IsCentrosymmetric (matrix_transpose M).
  Proof.
    exact _.
  Qed.
End CentrosymmetricType.

(** Addition and negation only require an abelian group of entries. *)
Section CentrosymmetricAbGroup.
  Context (A : AbGroup) (n : nat) (M N : Matrix A n n).
  Context `{!IsCentrosymmetric M} `{!IsCentrosymmetric N}.

  Goal IsCentrosymmetric (matrix_plus M N).
  Proof.
    exact _.
  Qed.

  Goal IsCentrosymmetric (matrix_negate M).
  Proof.
    exact _.
  Qed.
End CentrosymmetricAbGroup.

