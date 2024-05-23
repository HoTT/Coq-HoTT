Require Import Basics.Overture Basics.Trunc Basics.Tactics Basics.Decidable.
Require Import Types.Sigma.
Require Import Spaces.List.Core Spaces.List.Theory Spaces.List.Paths.
Require Import Algebra.Rings.Ring Algebra.Rings.Module Algebra.Rings.CRing
  Algebra.Rings.KroneckerDelta Algebra.Rings.Vector.
Require Import abstract_algebra.

Set Universe Minimization ToSet.

Local Open Scope mc_scope.

(** * Matrices *)

(** ** Definition *)

Definition Matrix (R : Type@{i}) (m n : nat) : Type@{i}
  := Vector (Vector R n) m.

Global Instance istrunc_matrix (R : Type) k `{IsTrunc k.+2 R} m n
  : IsTrunc k.+2 (Matrix R m n)
  := _.

(** Building a matrix from a function that takes row and column indices. *)
Definition Build_Matrix (R : Type) (m n : nat)
  (M_fun : forall (i : nat) (j : nat), (i < m)%nat -> (j < n)%nat -> R)
  : Matrix R m n.
Proof.
  snrapply Build_Vector.
  intros i Hi.
  snrapply Build_Vector.
  intros j Hj.
  exact (M_fun i j Hi Hj).
Defined.

(** The entry at row [i] and column [j] of a matrix [M]. *)
Definition entry {R : Type} {m n} (M : Matrix R m n) (i j : nat)
  {H1 : (i < m)%nat} {H2 : (j < n)%nat}
  : R
  := Vector.entry (Vector.entry M i) j.

(** Mapping a function on all the entries of a matrix. *)
Definition matrix_map {R S : Type} {m n} (f : R -> S)
  : Matrix R m n -> Matrix S m n
  := fun M => Build_Matrix S m n (fun i j _ _ => f (entry M i j)).

Definition matrix_map2 {R S T : Type} {m n} (f : R -> S -> T)
  : Matrix R m n -> Matrix S m n -> Matrix T m n
  := fun M N => Build_Matrix T m n
    (fun i j _ _ => f (entry M i j) (entry N i j)).

(** The [(i, j)]-entry of [Build_Matrix R m n M_fun] is [M_fun i j]. *)
Definition entry_Build_Matrix {R : Type} {m n}
  (M_fun : forall i j, (i < m)%nat -> (j < n)%nat -> R)
  (i j : nat) (H1 : (i < m)%nat) (H2 : (j < n)%nat)
  : entry (Build_Matrix R m n M_fun) i j = M_fun i j _ _.
Proof.
  unfold entry.
  by rewrite 2 entry_Build_Vector.
Defined.

(** Two matrices are equal if all their entries are equal. *)
Definition path_matrix {R : Type} {m n} (M N : Matrix R m n)
  (H : forall i j (Hi : (i < m)%nat) (Hj : (j < n)%nat), entry M i j = entry N i j)
  : M = N.
Proof.
  snrapply path_vector.
  intros i Hi.
  snrapply path_vector.
  intros j Hj.
  exact (H i j Hi Hj).
Defined.

(** ** Addition and module structure *)

(** Here we define the abelian group of (n x m)-matrices over a ring. This follows from the abelian group structure of the underlying vectors. We are also able to derive a left module strucutre when the entries come from a left module. *)

Definition abgroup_matrix (A : AbGroup) (m n : nat) : AbGroup
  := abgroup_vector (abgroup_vector A n) m.

Definition matrix_plus {A : AbGroup} {m n}
  : Matrix A m n -> Matrix A m n -> Matrix A m n
  := @sg_op (abgroup_matrix A m n) _.

Definition matrix_zero (A : AbGroup) m n : Matrix A m n
  := @mon_unit (abgroup_matrix A m n) _. 

Global Instance isleftmodule_isleftmodule_matrix (A : AbGroup) (m n : nat)
  {R : Ring} `{IsLeftModule R A}
  : IsLeftModule R (abgroup_matrix A m n).
Proof.
  snrapply isleftmodule_isleftmodule_vector.
  snrapply isleftmodule_isleftmodule_vector.
  exact _.
Defined.

(** As a special case, we get the left module of matrices over a ring. *)
Global Instance isleftmodule_abgroup_matrix (R : Ring) (m n : nat)
  : IsLeftModule R (abgroup_matrix R m n)
  := _.

Definition matrix_scale {R : Ring} {m n : nat} (r : R) (M : Matrix R m n)
  : Matrix R m n
  := lact r M.  

(** ** Multiplication *)

(** Matrix multiplication is defined such that the entry at row [i] and column [j] of the resulting matrix is the sum of the products of the corresponding entries from the [i]th row of the first matrix and the [j]th column of the second matrix. Matrices correspond to module homomorphisms between free modules of finite rank (think vector spaces), and matrix multiplication represents the composition of these homomorphisms. **)
Definition matrix_mult {R : Ring@{i}} {m n k : nat} (M : Matrix R m n) (N : Matrix R n k)
  : Matrix R m k.
Proof.
  snrapply Build_Matrix.
  intros i j Hi Hj.
  exact (ab_sum n (fun k Hk => entry M i k * entry N k j)).
Defined.

(** TODO move *)
Definition diagonal_matrix {R : Ring@{i}} {n : nat} (v : list R) (p : length v = n)
  : Matrix R n n.
Proof.
  snrapply Build_Matrix.
  intros i j H1 H2.
  destruct (dec (i = j)).
  - destruct p.
    exact (nth' v i H1).
  - exact 0.
Defined.

(** The identity matrix is the matrix with ones on the diagonal and zeros elsewhere. It acts as the multiplicative identity for matrix multiplication. We define it here using the [kronecker_delta] function which will make proving properties about it conceptually easier later. *)
Definition identity_matrix (R : Ring@{i}) (n : nat) : Matrix R n n
  := Build_Matrix R n n (fun i j _ _ => kronecker_delta i j).

(** This is the most general statement of associativity for matrix multiplication. *)
Definition associative_matrix_mult (R : Ring@{i}) (m n p q : nat)
  : HeteroAssociative
      (@matrix_mult R m n q) (@matrix_mult R n p q)
      (@matrix_mult R m p q) (@matrix_mult R m n p).
Proof.
  intros M N P; nrapply path_matrix; intros i j Hi Hj.
  rewrite 2 entry_Build_Matrix.
  lhs nrapply path_ab_sum.
  { intros k Hk.
    rewrite entry_Build_Matrix.
    apply rng_sum_dist_l. }
  lhs nrapply ab_sum_sum.
  rhs nrapply path_ab_sum.
  2: intros k Hk; by rewrite entry_Build_Matrix.
  nrapply path_ab_sum.
  intros k Hk.
  rhs nrapply rng_sum_dist_r.
  nrapply path_ab_sum.
  intros l Hl.
  apply associativity.
Defined.

(** Matrix multiplication distributes over addition of matrices on the left. *)
Definition left_distribute_matrix_mult (R : Ring@{i}) (m n p : nat)
  : LeftHeteroDistribute (@matrix_mult R m n p) matrix_plus matrix_plus.
Proof.
  intros M N P; apply path_matrix; intros i j Hi Hj.
  rewrite !entry_Build_Matrix, !entry_Build_Vector.
  change (?x = ?y + ?z) with (x = sg_op y z).
  rewrite <- ab_sum_plus.
  nrapply path_ab_sum.
  intros k Hk.
  rewrite entry_Build_Matrix.
  apply rng_dist_l.
Defined.

(** Matrix multiplication distributes over addition of matrices on the right. *)
Definition right_distribute_matrix_mult (R : Ring@{i}) (m n p : nat)
  : RightHeteroDistribute (@matrix_mult R m n p) matrix_plus matrix_plus.
Proof.
  intros M N P; apply path_matrix; intros i j Hi Hj.
  rewrite !entry_Build_Matrix, !entry_Build_Vector.
  change (?x = ?y + ?z) with (x = sg_op y z).
  rewrite <- ab_sum_plus.
  nrapply path_ab_sum.
  intros k Hk.
  rewrite entry_Build_Matrix.
  apply rng_dist_r.
Defined.

(** The identity matrix acts as a left identity for matrix multiplication. *)
Definition left_identity_matrix_mult (R : Ring@{i}) (m n: nat)
  : LeftIdentity (@matrix_mult R m m n) (identity_matrix R m).
Proof.
  intros M; apply path_matrix; intros i j Hi Hj.
  rewrite entry_Build_Matrix.
  lhs nrapply path_ab_sum.
  1: intros k Hk; by rewrite entry_Build_Matrix.
  nrapply rng_sum_kronecker_delta_l.
Defined.

(** The identity matrix acts as a right identity for matrix multiplication. *)
Definition right_identity_matrix_mult (R : Ring@{i}) (m n : nat)
  : RightIdentity (@matrix_mult R m n n) (identity_matrix R n).
Proof.
  intros M; apply path_matrix; intros i j Hi Hj.
  rewrite entry_Build_Matrix.
  lhs nrapply path_ab_sum.
  1: intros k Hk; by rewrite entry_Build_Matrix.
  nrapply rng_sum_kronecker_delta_r'.
Defined.

(** TODO: define this as an R-algebra *)
(** Matrices over a ring form a (generally) non-commutative ring. *)
Definition matrix_ring (R : Ring@{i}) (n : nat) : Ring.
Proof.
  snrapply Build_Ring.
  6: repeat split.
  - exact (abgroup_matrix R n n).
  - exact matrix_mult.
  - exact (identity_matrix R n).
  - exact (left_distribute_matrix_mult R n n n).
  - exact (right_distribute_matrix_mult R n n n).
  - exact _.
  - exact (associative_matrix_mult R n n n n).
  - exact (left_identity_matrix_mult R n n).
  - exact (right_identity_matrix_mult R n n).
Defined.

(** ** Transpose *)

(** The transpose of a matrix is the matrix with the rows and columns swapped. *)
Definition matrix_transpose {R : Type} {m n} : Matrix R m n -> Matrix R n m
  := fun M => Build_Matrix R n m (fun i j H1 H2 => entry M j i).

(** Tranposing a matrix is involutive. *)
Definition matrix_transpose_transpose {R : Type} {m n} (M : Matrix R m n)
  : matrix_transpose (matrix_transpose M) = M.
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  lhs nrapply entry_Build_Matrix.
  nrapply entry_Build_Matrix.
Defined.

(** Transpose distributes over addition. *)
Definition matrix_transpose_plus {R : Ring} {m n} (M N : Matrix R m n)
  : matrix_transpose (matrix_plus M N)
    = matrix_plus (matrix_transpose M) (matrix_transpose N).
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  by rewrite !entry_Build_Matrix, !entry_Build_Vector.
Defined.

(** Transpose commutes with scalar multiplication. *)
Definition matrix_transpose_scale {R : Ring} {m n} (r : R) (M : Matrix R m n)
  : matrix_transpose (matrix_scale r M)
    = matrix_scale r (matrix_transpose M).
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  by rewrite !entry_Build_Matrix, !entry_Build_Vector.
Defined.

(** Transpose distributes over multiplication (in a commutative ring). *)
Definition matrix_transpose_mult {R : CRing} {m n p}
  (M : Matrix R m n) (N : Matrix R n p)
  : matrix_transpose (matrix_mult M N)
    = matrix_mult (matrix_transpose N) (matrix_transpose M).
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  rewrite 3 entry_Build_Matrix.
  apply path_ab_sum.
  intros k Hk.
  rewrite 2 entry_Build_Matrix.
  apply rng_mult_comm.
Defined.

(** ** Trace *)

(** The trace of a square matrix is the sum of the diagonal entries. *)
Definition matrix_trace {R : Ring} {n} (M : Matrix R n n) : R
  := ab_sum n (fun i Hi => entry M i i).

(** The trace of a matrix multiplication is the same as the trace of the reverse multiplication. *)
Definition matrix_trace_mult {R : CRing} {n} (M N : Matrix R n n)
  : matrix_trace (matrix_mult M N) = matrix_trace (matrix_mult N M).
Proof.
  lhs nrapply path_ab_sum.
  { intros i Hi.
    lhs nrapply entry_Build_Matrix.
    nrapply path_ab_sum.
    { intros j Hj.
      apply rng_mult_comm. } }
  lhs nrapply ab_sum_sum. 
  apply path_ab_sum.
  intros i Hi.
  rhs nrapply entry_Build_Matrix.
  reflexivity.
Defined.

(** The trace of the transpose of a matrix is the same as the trace of the matrix. *)
Definition trace_transpose {R : Ring} {n} (M : Matrix R n n)
  : matrix_trace (matrix_transpose M) = matrix_trace M.
Proof.
  apply path_ab_sum.
  intros i Hi.
  nrapply entry_Build_Matrix.
Defined.

(** ** Matrix minors *)

Definition skip (n : nat) : nat -> nat
  := fun i => if dec (i < n)%nat then i else i.+1%nat.

Global Instance isinjective_skip n : IsInjective (skip n).
Proof.
  hnf.
  intros x y p.
  unfold skip in p.
  destruct (dec (x < n)%nat) as [H|H], (dec (y < n)%nat) as [H'|H'].
  - exact p.
  - destruct p^.
    contradiction (H' (leq_trans _ H)).
  - destruct p.
    contradiction (H (leq_trans _ H')).
  - by apply path_nat_S.
Defined.

Local Instance lt_n1_skip k i n (H : (i < n.+1)%nat) (H' : (k < n)%nat)
  : (skip i k < n.+1)%nat.
Proof.
  unfold skip.
  destruct (dec (k < i))%nat as [H''|H''].
  - exact (transitive_lt _ _ _ H'' H) .
  - apply leq_S_n'.
    exact H'.
Defined.

Definition matrix_minor {R : Ring@{i}} {n : nat} (i j : nat)
  {Hi : (i < n.+1)%nat} {Hj : (j < n.+1)%nat} (M : Matrix R n.+1 n.+1)
  : Matrix R n n
  := Build_Matrix R n n (fun k l _ _ => entry M (skip i k) (skip j l)).

(** A minor of the zero matrix is again the zero matrix. *)
Definition matrix_minor_zero {R : Ring@{i}} {n : nat} (i j : nat)
  (Hi : (i < n.+1)%nat) (Hj : (j < n.+1)%nat)
  : matrix_minor i j (matrix_zero R n.+1 n.+1) = matrix_zero R n n.
Proof.
  apply path_matrix.
  intros k l Hk Hl.
  by rewrite !entry_Build_Matrix.
Defined.

Definition matrix_minor_identity {R : Ring@{i}} {n : nat}
  (i : nat) (Hi : (i < n.+1)%nat)
  : matrix_minor i i (identity_matrix R n.+1) = identity_matrix R n.
Proof.
  apply path_matrix.
  intros j k Hj Hk.
  rewrite 3 entry_Build_Matrix.
  rapply kronecker_delta_map_inj.
Defined.

Definition matrix_minor_plus {R : Ring@{i}} {n : nat} (i j : nat)
  (Hi : (i < n.+1)%nat) (Hj : (j < n.+1)%nat) (M N : Matrix R n.+1 n.+1)
  : matrix_minor i j (matrix_plus M N)
    = matrix_plus (matrix_minor i j M) (matrix_minor i j N).
Proof.
  apply path_matrix.
  intros k l Hk Hl.
  by rewrite !entry_Build_Matrix, !entry_Build_Vector.
Defined.

Definition matrix_minor_scale {R : Ring@{i}} {n : nat} (i j : nat)
  (Hi : (i < n.+1)%nat) (Hj : (j < n.+1)%nat) (r : R) (M : Matrix R n.+1 n.+1)
  : matrix_minor i j (matrix_scale r M) = matrix_scale r (matrix_minor i j M).
Proof.
  apply path_matrix.
  intros k l Hk Hl.
  by rewrite !entry_Build_Matrix, !entry_Build_Vector.
Defined.

Definition matrix_minor_transpose {R : Ring@{i}} {n : nat} (i j : nat)
  (Hi : (i < n.+1)%nat) (Hj : (j < n.+1)%nat) (M : Matrix R n.+1 n.+1)
  : matrix_minor j i (matrix_transpose M)
    = matrix_transpose (matrix_minor i j M).
Proof.
  apply path_matrix.
  intros k l Hk Hl.
  by rewrite 4 entry_Build_Matrix.
Defined.
