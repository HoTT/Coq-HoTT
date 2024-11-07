Require Import Basics.Overture Basics.Trunc Basics.Tactics Basics.Decidable.
Require Import Types.Sigma.
Require Import Spaces.List.Core Spaces.List.Theory Spaces.List.Paths.
Require Import Algebra.Rings.Ring Algebra.Rings.Module Algebra.Rings.CRing
  Algebra.Rings.KroneckerDelta Algebra.Rings.Vector.
Require Import abstract_algebra.
Require Import WildCat.Core WildCat.Paths.
Require Import Modalities.ReflectiveSubuniverse.

Set Universe Minimization ToSet.

Local Open Scope mc_scope.

(** * Matrices *)

(** ** Definition *)

Definition Matrix@{i} (R : Type@{i}) (m n : nat) : Type@{i}
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

(** The length conditions here are decidable so can be inferred in proofs. *)
Definition Build_Matrix' (R : Type) (m n : nat)
  (l : list (list R))
  (wf_row : length l = m)
  (wf_col : for_all (fun row => length row = n) l)
  : Matrix R m n.
Proof.
  snrefine (_; _).
  - snrapply list_sigma.
    + exact l.
    + exact wf_col.
  - by lhs nrapply length_list_sigma.
Defined.

Definition entries@{i|} {R : Type@{i}} {m n} (M : Matrix R m n)
  : list (list R)
  := list_map@{i i} pr1 (pr1 M).

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

Definition matrix_negate {A : AbGroup} {m n}
  : Matrix A m n -> Matrix A m n
  := @negate (abgroup_matrix A m n) _.

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

Definition matrix_lact {R : Ring} {m n : nat} (r : R) (M : Matrix R m n)
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

(** The identity matrix is the matrix with ones on the diagonal and zeros elsewhere. It acts as the multiplicative identity for matrix multiplication. We define it here using the [kronecker_delta] function which will make proving properties about it conceptually easier later. *)
Definition identity_matrix (R : Ring@{i}) (n : nat) : Matrix R n n
  := Build_Matrix R n n (fun i j _ _ => kronecker_delta i j).

(** This is the most general statement of associativity for matrix multiplication. *)
Definition associative_matrix_mult (R : Ring) (m n p q : nat)
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
Definition left_distribute_matrix_mult (R : Ring) (m n p : nat)
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
Definition right_distribute_matrix_mult (R : Ring) (m n p : nat)
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
Definition left_identity_matrix_mult (R : Ring) (m n: nat)
  : LeftIdentity (@matrix_mult R m m n) (identity_matrix R m).
Proof.
  intros M; apply path_matrix; intros i j Hi Hj.
  rewrite entry_Build_Matrix.
  lhs nrapply path_ab_sum.
  1: intros k Hk; by rewrite entry_Build_Matrix.
  nrapply rng_sum_kronecker_delta_l.
Defined.

(** The identity matrix acts as a right identity for matrix multiplication. *)
Definition right_identity_matrix_mult (R : Ring) (m n : nat)
  : RightIdentity (@matrix_mult R m n n) (identity_matrix R n).
Proof.
  intros M; apply path_matrix; intros i j Hi Hj.
  rewrite entry_Build_Matrix.
  lhs nrapply path_ab_sum.
  1: intros k Hk; by rewrite entry_Build_Matrix.
  nrapply rng_sum_kronecker_delta_r'.
Defined.

(** TODO: define this as an R-algebra. What is an R-algebra over a non-commutative right however? (Here we have a bimodule which might be important) *)
(** Matrices over a ring form a (generally) non-commutative ring. *)
Definition matrix_ring (R : Ring@{i}) (n : nat) : Ring.
Proof.
  snrapply Build_Ring.
  - exact (abgroup_matrix R n n).
  - exact matrix_mult.
  - exact (identity_matrix R n).
  - exact (associative_matrix_mult R n n n n).
  - exact (left_distribute_matrix_mult R n n n).
  - exact (right_distribute_matrix_mult R n n n).
  - exact (left_identity_matrix_mult R n n).
  - exact (right_identity_matrix_mult R n n).
Defined.

(** Matrix multiplication on the right preserves scalar multiplication in the sense that [matrix_lact r (matrix_mult M N) = matrix_mult (matrix_lact r M) N] for [r] a ring element and [M] and [N] matrices of compatible sizes. *)
Definition matrix_mult_lact_l {R : Ring} {m n p : nat}
  : HeteroAssociative (@matrix_lact R m p) (@matrix_mult R m n p)
      (@matrix_mult R m n p) (@matrix_lact R m n).
Proof.
  intros r M N.
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite !entry_Build_Matrix, !entry_Build_Vector. 
  lhs nrapply rng_sum_dist_l.
  snrapply path_ab_sum.
  intros k Hk; cbn.
  rewrite !entry_Build_Matrix.
  snrapply rng_mult_assoc.
Defined.

(** The same doesn't hold for the right matrix, since the ring is not commutative. However we could say an analagous statement for the right action. We haven't yet stated a definition of right module yet though. *)

(** In a commutative ring, matrix multiplication over the ring and the opposite ring agree. *)
Definition matrix_mult_rng_op {R : CRing} {m n p}
  (M : Matrix R m n) (N : Matrix R n p)
  : matrix_mult (R:=rng_op R) M N = matrix_mult M N.
Proof.
  apply path_matrix; intros i j Hi Hj.
  rewrite 2 entry_Build_Matrix.
  apply path_ab_sum; intros k Hk.
  apply rng_mult_comm.
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
Definition matrix_transpose_lact {R : Ring} {m n} (r : R) (M : Matrix R m n)
  : matrix_transpose (matrix_lact r M)
    = matrix_lact r (matrix_transpose M).
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  by rewrite !entry_Build_Matrix, !entry_Build_Vector.
Defined.

(** The negation of a transposed matrix is the same as the transposed matrix of the negation. *)
Definition matrix_transpose_negate {R : Ring} {m n} (M : Matrix R m n)
  : matrix_transpose (matrix_negate M) = matrix_negate (matrix_transpose M).
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  by rewrite !entry_Build_Matrix, !entry_Build_Vector.
Defined.

(** Transpose distributes over multiplication when you reverse the ring multiplication. *)
Definition matrix_transpose_mult {R : Ring} {m n p}
  (M : Matrix R m n) (N : Matrix R n p)
  : matrix_transpose (matrix_mult M N)
    = matrix_mult (R:=rng_op R) (matrix_transpose N) (matrix_transpose M).
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  rewrite 3 entry_Build_Matrix.
  apply path_ab_sum.
  intros k Hk.
  rewrite 2 entry_Build_Matrix.
  reflexivity.
Defined.

(** When the ring is commutative, there is no need to reverse the multiplication. *)
Definition matrix_transpose_mult_comm {R : CRing} {m n p}
  (M : Matrix R m n) (N : Matrix R n p)
  : matrix_transpose (matrix_mult M N)
    = matrix_mult (matrix_transpose N) (matrix_transpose M).
Proof.
  lhs nrapply matrix_transpose_mult.
  apply matrix_mult_rng_op.
Defined.

(** The transpose of the zero matrix is the zero matrix. *)
Definition matrix_transpose_zero {R : Ring} {m n}
  : matrix_transpose (matrix_zero R m n) = matrix_zero R n m.
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  by rewrite !entry_Build_Matrix.
Defined.

(** The transpose of the identity matrix is the identity matrix. *)
Definition matrix_transpose_identity@{i} {R : Ring@{i}} {n}
  : matrix_transpose (identity_matrix R n) = identity_matrix R n.
Proof.
  apply path_matrix.
  intros i j Hi Hj.
  rewrite 3 entry_Build_Matrix.
  apply kronecker_delta_symm.
Defined.

(** ** Diagonal matrices *)

(** A diagonal matrix is a matrix with zeros everywhere except on the diagonal. Its entries are given by a vector. *)
Definition matrix_diag {R : Ring@{i}} {n : nat} (v : Vector R n)
  : Matrix R n n.
Proof.
  snrapply Build_Matrix.
  intros i j H1 H2.
  exact (kronecker_delta i j * Vector.entry v i).
Defined.

(** Addition of diagonal matrices is the same as addition of the corresponding vectors. *)
Definition matrix_diag_plus {R : Ring@{i}} {n : nat} (v w : Vector R n)
  : matrix_plus (matrix_diag v) (matrix_diag w) = matrix_diag (vector_plus v w).
Proof.
  symmetry.
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite 2 entry_Build_Matrix, 5 entry_Build_Vector.
  nrapply rng_dist_l.
Defined.

(** Matrix multiplication of diagonal matrices is the same as multiplying the corresponding vectors pointwise. *)
Definition matrix_diag_mult {R : Ring} {n : nat} (v w : Vector R n)
  : matrix_mult (matrix_diag v) (matrix_diag w)
    = matrix_diag (vector_map2 (.*.) v w).
Proof.
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite 2 entry_Build_Matrix.
  lhs snrapply path_ab_sum.
  { intros k Hk.
    rewrite 2 entry_Build_Matrix.
    rewrite rng_mult_assoc.
    rewrite <- (rng_mult_assoc (kronecker_delta _ _)).
    rewrite kronecker_delta_comm.
    rewrite <- 2 rng_mult_assoc.
    reflexivity. }
  rewrite (rng_sum_kronecker_delta_l _ _ Hi).
  by rewrite entry_Build_Vector.
Defined.

(** The transpose of a diagonal matrix is the same diagonal matrix. *)
Definition matrix_transpose_diag {R : Ring@{i}} {n : nat} (v : Vector R n)
  : matrix_transpose (matrix_diag v) = matrix_diag v.
Proof.
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite 3 entry_Build_Matrix.
  rewrite kronecker_delta_symm.
  unfold kronecker_delta.
  destruct (dec (i = j)) as [p|np].
  1: f_ap; symmetry; by apply path_entry_vector.
  by rewrite !rng_mult_zero_l.
Defined.

(** The diagonal matrix construction is injective. *)
Global Instance isinj_matrix_diag {R : Ring@{i}} {n : nat}
  : IsInjective (@matrix_diag R n).
Proof.
  intros v1 v2 p.
  snrapply path_vector.
  intros i Hi.
  apply (ap (fun M => entry M i i)) in p.
  rewrite 2 entry_Build_Matrix in p.
  rewrite kronecker_delta_refl in p.
  by rewrite 2 rng_mult_one_l in p.
Defined.

(** A matrix is diagonal if it is equal to a diagonal matrix. *)
Class IsDiagonal@{i} {R : Ring@{i}} {n : nat} (M : Matrix R n n) : Type@{i} := {
  isdiagonal_diag_vector : Vector R n;
  isdiagonal_diag : M = matrix_diag isdiagonal_diag_vector;
}.

Arguments isdiagonal_diag_vector {R n} M {_}.
Arguments isdiagonal_diag {R n} M {_}.

Definition issig_IsDiagonal {R : Ring@{i}} {n : nat} {M : Matrix R n n}
  : _ <~> IsDiagonal M
  := ltac:(issig).

(** A matrix is diagonal in a unique way. *)
Global Instance ishprop_isdiagonal {R : Ring@{i}} {n : nat} (M : Matrix R n n)
  : IsHProp (IsDiagonal M).
Proof.
  snrapply hprop_allpath.
  intros x y.
  snrapply ((equiv_ap' issig_IsDiagonal^-1%equiv _ _ )^-1%equiv).
  rapply path_sigma_hprop; cbn.
  apply isinj_matrix_diag.
  exact ((isdiagonal_diag M)^ @ isdiagonal_diag M).
Defined.

(** The zero matrix is diagonal. *)
Global Instance isdiagonal_matrix_zero {R : Ring@{i}} {n : nat}
  : IsDiagonal (matrix_zero R n n).
Proof.
  exists (vector_zero R n).
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite 2 entry_Build_Matrix, entry_Build_Vector.
  by rewrite rng_mult_zero_r.
Defined.

(** The identity matrix is diagonal. *)
Global Instance isdiagonal_identity_matrix {R : Ring@{i}} {n : nat}
  : IsDiagonal (identity_matrix R n).
Proof.
  exists (Build_Vector R n (fun _ _ => 1)).
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite 2 entry_Build_Matrix, entry_Build_Vector.
  by rewrite rng_mult_one_r.
Defined.

(** The sum of two diagonal matrices is diagonal. *)
Global Instance isdiagonal_matrix_plus {R : Ring@{i}} {n : nat}
  (M N : Matrix R n n) `{IsDiagonal R n M} `{IsDiagonal R n N}
  : IsDiagonal (matrix_plus M N).
Proof.
  exists (vector_plus (isdiagonal_diag_vector M) (isdiagonal_diag_vector N)).
  rewrite (isdiagonal_diag M), (isdiagonal_diag N).
  apply matrix_diag_plus.
Defined.

(** The negative of a diagonal matrix is diagonal. *)
Global Instance isdiagonal_matrix_negate {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{IsDiagonal R n M}
  : IsDiagonal (matrix_negate M).
Proof.
  exists (vector_neg _ _ (isdiagonal_diag_vector M)).
  rewrite (isdiagonal_diag M).
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite !entry_Build_Matrix, !entry_Build_Vector.
  by rewrite rng_mult_negate_r.
Defined.

(** The product of two diagonal matrices is diagonal. *)
Global Instance isdiagonal_matrix_mult {R : Ring@{i}} {n : nat}
  (M N : Matrix R n n) `{IsDiagonal R n M} `{IsDiagonal R n N}
  : IsDiagonal (matrix_mult M N).
Proof.
  exists (vector_map2 (.*.) (isdiagonal_diag_vector M) (isdiagonal_diag_vector N)).
  rewrite (isdiagonal_diag M), (isdiagonal_diag N).
  apply matrix_diag_mult.
Defined.

(** The transpose of a diagonal matrix is diagonal. *)
Global Instance isdiagonal_matrix_transpose {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{IsDiagonal R n M}
  : IsDiagonal (matrix_transpose M).
Proof.
  exists (isdiagonal_diag_vector M).
  rewrite (isdiagonal_diag M).
  apply matrix_transpose_diag.
Defined.

(** Given a square matrix, we can extract the diagonal as a vector. *)
Definition matrix_diag_vector {R : Ring} {n : nat} (M : Matrix R n n)
  : Vector R n
  := Build_Vector R n (fun i _ => entry M i i).

(** Diagonal matrices form a subring of the ring of square matrices. *)
Definition matrix_diag_ring@{i} (R : Ring@{i}) (n : nat)
  : Subring@{i i} (matrix_ring R n).
Proof.
  snrapply (Build_Subring' (fun M : matrix_ring R n => IsDiagonal M) _); hnf.
  - intros; exact _.
  - intros x y dx dy.
    nrapply isdiagonal_matrix_plus; trivial.
    by nrapply isdiagonal_matrix_negate.
  - nrapply isdiagonal_matrix_mult.
  - nrapply isdiagonal_identity_matrix.
Defined.

(** ** Trace *)

(** The trace of a square matrix is the sum of the diagonal entries. *)
Definition matrix_trace {R : Ring} {n} (M : Matrix R n n) : R
  := ab_sum n (fun i Hi => entry M i i).

(** The trace of a matrix preserves addition. *)
Definition matrix_trace_plus {R : Ring} {n} (M N : Matrix R n n)
  : matrix_trace (matrix_plus M N) = (matrix_trace M) + (matrix_trace N).
Proof.
  unfold matrix_trace.
  lhs nrapply path_ab_sum.
  { intros i Hi.
    by rewrite entry_Build_Matrix. }
  by rewrite ab_sum_plus.
Defined.

(** The trace of a matrix preserves scalar multiplication. *)
Definition matrix_trace_lact {R : Ring} {n} (r : R) (M : Matrix R n n)
  : matrix_trace (matrix_lact r M) = r * matrix_trace M.
Proof.
  unfold matrix_trace.
  rewrite rng_sum_dist_l.
  apply path_ab_sum.
  intros i Hi.
  by rewrite entry_Build_Matrix.
Defined.

(** The trace of a matrix multiplication is the same as the trace of the reverse multiplication. This holds only in a commutative ring. *)
Definition matrix_trace_mult {R : CRing} {m n : nat}
  (M : Matrix R m n) (N : Matrix R n m)
  : matrix_trace (matrix_mult M N) = matrix_trace (matrix_mult N M).
Proof.
  lhs nrapply path_ab_sum.
  { intros i Hi.
    lhs nrapply entry_Build_Matrix.
    nrapply path_ab_sum.
    intros j Hj.
    apply rng_mult_comm. }
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
  - by apply path_nat_succ.
Defined.

Local Instance lt_n1_skip k i n (H : (i < n.+1)%nat) (H' : (k < n)%nat)
  : (skip i k < n.+1)%nat.
Proof.
  unfold skip.
  destruct (dec (k < i))%nat as [H''|H'']; exact _.
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
  : matrix_minor i j (matrix_lact r M) = matrix_lact r (matrix_minor i j M).
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

(** ** Triangular matrices *)

(** A matrix is upper triangular if all the entries below the diagonal are zero. *)
Class IsUpperTriangular@{i} {R : Ring@{i}} {n : nat} (M : Matrix@{i} R n n) : Type@{i}
  := upper_triangular
  : merely@{i} (forall i j (Hi : (i < n)%nat) (Hj : (j < n)%nat), (i < j)%nat -> entry M i j = 0).

Global Instance ishprop_isuppertriangular@{i} {R : Ring@{i}} {n : nat} (M : Matrix R n n)
  : IsHProp (IsUpperTriangular M).
Proof.
  apply istrunc_truncation@{i i}.
Defined.

(** A matrix is lower triangular if all the entries above the diagonal are zero. We define it as the transpose being upper triangular. *)
Class IsLowerTriangular {R : Ring@{i}} {n : nat} (M : Matrix@{i} R n n) : Type@{i}
  := upper_triangular_transpose :: IsUpperTriangular (matrix_transpose M).

Global Instance ishprop_islowertriangular@{i} {R : Ring@{i}} {n : nat}
  (M : Matrix R n n)
  : IsHProp (IsLowerTriangular M).
Proof.
  apply istrunc_truncation@{i i}.
Defined.

(** The transpose of a matrix is lower triangular if and only if the matrix is upper triangular. *)
Global Instance lower_triangular_transpose {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsUpperTriangular M}
  : IsLowerTriangular (matrix_transpose M).
Proof.
  unfold IsLowerTriangular.
  by rewrite matrix_transpose_transpose.
Defined.

(** The sum of two upper triangular matrices is upper triangular. *)
Global Instance upper_triangular_plus@{i} {R : Ring@{i}} {n : nat} (M N : Matrix R n n)
  {H1 : IsUpperTriangular M} {H2 : IsUpperTriangular N}
  : IsUpperTriangular (matrix_plus M N).
Proof.
  unfold IsUpperTriangular.
  (* We use [strip_reflections] rather than [strip_truncations] here and below because it generates fewer universe variables in some versions of Coq. *)
  strip_reflections; apply tr.
  intros i j Hi Hj lt_i_j.
  specialize (H1 i j Hi Hj lt_i_j).
  specialize (H2 i j Hi Hj lt_i_j).
  rewrite entry_Build_Matrix.
  change (Vector.entry (Vector.entry ?M ?i) ?j) with (entry M i j).
  rewrite H1, H2.
  by rewrite rng_plus_zero_l.
Defined.

(** The sum of two lower triangular matrices is lower triangular. *)
Global Instance lower_triangular_plus {R : Ring@{i}} {n : nat}
  (M N : Matrix R n n) `{!IsLowerTriangular M} `{!IsLowerTriangular N}
  : IsLowerTriangular (matrix_plus M N).
Proof.
  unfold IsLowerTriangular.
  rewrite matrix_transpose_plus.
  by apply upper_triangular_plus.
Defined.

(** The negation of an upper triangular matrix is upper triangular. *)
Global Instance upper_triangular_negate@{i} {R : Ring@{i}} {n : nat} (M : Matrix R n n)
  {H : IsUpperTriangular M}
  : IsUpperTriangular (matrix_negate M).
Proof.
  unfold IsUpperTriangular.
  strip_reflections; apply tr.
  intros i j Hi Hj lt_i_j.
  rewrite entry_Build_Matrix.
  rewrite <- rng_negate_zero; f_ap.
  by nrapply H.
Defined.

(** The negation of a lower triangular matrix is lower triangular. *)
Global Instance lower_triangular_negate {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsLowerTriangular M}
  : IsLowerTriangular (matrix_negate M).
Proof.
  unfold IsLowerTriangular.
  rewrite matrix_transpose_negate.
  exact _.
Defined.

(** The product of two upper triangular matrices is upper triangular. *)
Global Instance upper_triangular_mult@{i} {R : Ring@{i}} {n : nat}
  (M N : Matrix R n n) {H1 : IsUpperTriangular M} {H2 : IsUpperTriangular N}
  : IsUpperTriangular (matrix_mult M N).
Proof.
  unfold IsUpperTriangular.
  strip_reflections; apply tr.
  intros i j Hi Hj lt_i_j.
  rewrite entry_Build_Matrix.
  apply ab_sum_zero.
  intros k Hk.
  destruct (dec (k <= i)%nat) as [leq_k_i|gt_k_i].
  { rewrite H2.
    1: by rewrite rng_mult_zero_r.
    rapply lt_leq_lt_trans. }
  apply gt_iff_not_leq in gt_k_i.
  rewrite H1.
  1: by rewrite rng_mult_zero_l.
  assumption.
Defined.

(** The product of two lower triangular matrices is lower triangular. *)
Global Instance lower_triangular_mult {R : Ring@{i}} {n : nat}
  (M N : Matrix R n n) {H1 : IsLowerTriangular M} {H2 : IsLowerTriangular N}
  : IsLowerTriangular (matrix_mult M N).
Proof.
  unfold IsLowerTriangular.
  rewrite matrix_transpose_mult.
  nrapply (upper_triangular_mult (R:=rng_op R)); assumption.
Defined.

(** The zero matrix is upper triangular. *)
Global Instance upper_triangular_zero {R : Ring@{i}} {n : nat}
  : IsUpperTriangular (matrix_zero R n n).
Proof.
  apply tr.
  by hnf; intros; rewrite entry_Build_Matrix.
Defined.

(** The zero matrix is lower triangular. *)
Global Instance lower_triangular_zero {R : Ring@{i}} {n : nat}
  : IsLowerTriangular (matrix_zero R n n).
Proof.
  unfold IsLowerTriangular.
  rewrite matrix_transpose_zero.
  exact _.
Defined.

(** The identity matrix is upper triangular. *)
Global Instance upper_triangular_identity@{i} {R : Ring@{i}} {n : nat}
  : IsUpperTriangular (identity_matrix R n).
Proof.
  unfold IsUpperTriangular.
  apply tr@{i}.
  intros i j Hi Hj lt_i_j.
  rewrite entry_Build_Matrix@{i}.
  by apply kronecker_delta_lt.
Defined.

(** The identity matrix is lower triangular. *)
Global Instance lower_triangular_identity@{i} {R : Ring@{i}} {n : nat}
  : IsLowerTriangular (identity_matrix R n).
Proof.
  unfold IsLowerTriangular.
  rewrite matrix_transpose_identity.
  exact _.
Defined.

(** A diagonal matrix is upper triangular. *)
Global Instance upper_triangular_diag {R : Ring@{i}} {n : nat} (v : Vector R n)
  : IsUpperTriangular (matrix_diag v).
Proof.
  unfold IsUpperTriangular.
  apply tr.
  intros i j Hi Hj lt_i_j.
  rewrite entry_Build_Matrix.
  rewrite kronecker_delta_lt.
  1: by rewrite rng_mult_zero_l.
  exact _.
Defined.

(** A diagonal matrix is lower triangular. *)
Global Instance lower_triangular_diag {R : Ring@{i}} {n : nat} (v : Vector R n)
  : IsLowerTriangular (matrix_diag v).
Proof.
  unfold IsLowerTriangular.
  rewrite matrix_transpose_diag.
  apply upper_triangular_diag.
Defined.

(** Upper triangular matrices are a subring of the ring of matrices. *)
Definition upper_triangular_matrix_ring@{i} (R : Ring@{i}) (n : nat)
  : Subring@{i i} (matrix_ring@{i} R n).
Proof.
  nrapply (Build_Subring' (fun M : matrix_ring R n => IsUpperTriangular M)).
  - exact _.
  (* These can all be found by typeclass search, but being explicit makes this faster. *)
  - intros x y ? ?; exact (upper_triangular_plus x (-y)).
  - exact upper_triangular_mult.
  - exact upper_triangular_identity.
Defined.

(** Lower triangular matrices are a subring of the ring of matrices. *)
Definition lower_triangular_matrix_ring@{i} (R : Ring@{i}) (n : nat)
  : Subring@{i i} (matrix_ring R n).
Proof.
  nrapply (Build_Subring'@{i i} (fun M : matrix_ring R n => IsLowerTriangular M)).
  - exact _.
  (* These can all be found by typeclass search, but being explicit makes this faster. *)
  - intros x y ? ?; exact (lower_triangular_plus x (-y)).
  - exact lower_triangular_mult.
  - exact lower_triangular_identity.
Defined.

(** ** Symmetric Matrices *)

(** A matrix is symmetric when it is equal to its transpose. *)
Class IsSymmetric {R : Ring@{i}} {n : nat} (M : Matrix@{i} R n n) : Type@{i}
  := matrix_transpose_issymmetric : matrix_transpose M = M.

Arguments matrix_transpose_issymmetric {R n} M {_}.

(** The zero matrix is symmetric. *)
Global Instance issymmetric_matrix_zero {R : Ring@{i}} {n : nat}
  : IsSymmetric (matrix_zero R n n)
  := matrix_transpose_zero.

(** The identity matrix is symmetric. *)
Global Instance issymmetric_matrix_identity {R : Ring@{i}} {n : nat}
  : IsSymmetric (identity_matrix R n)
  := matrix_transpose_identity.

(** The sum of two symmetric matrices is symmetric. *)
Global Instance issymmetric_matrix_plus {R : Ring@{i}} {n : nat}
  (M N : Matrix R n n) `{!IsSymmetric M} `{!IsSymmetric N}
  : IsSymmetric (matrix_plus M N).
Proof.
  unfold IsSymmetric.
  rewrite matrix_transpose_plus.
  f_ap.
Defined.

(** The negation of a symmetric matrix is symmetric. *)
Global Instance issymmetric_matrix_negate {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsSymmetric M}
  : IsSymmetric (matrix_negate M).
Proof.
  unfold IsSymmetric.
  rewrite matrix_transpose_negate.
  f_ap.
Defined.

(** A scalar multiple of a symmetric matrix is symmetric. *)
Global Instance issymmetric_matrix_scale {R : Ring@{i}} {n : nat}
  (r : R) (M : Matrix R n n) `{!IsSymmetric M}
  : IsSymmetric (matrix_lact r M).
Proof.
  unfold IsSymmetric.
  rewrite matrix_transpose_lact.
  f_ap.
Defined.

(** The transpose of a symmetric matrix is symmetric. *)
Global Instance issymmetric_matrix_transpose {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsSymmetric M}
  : IsSymmetric (matrix_transpose M).
Proof.
  unfold IsSymmetric.
  rewrite matrix_transpose_transpose.
  by symmetry.
Defined.

(** A symmetric upper triangular matrix is diagonal. *)
Global Instance isdiagonal_upper_triangular_issymmetric {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsSymmetric M} {H : IsUpperTriangular M}
  : IsDiagonal M.
Proof.
  exists (matrix_diag_vector M).
  snrapply path_matrix.
  intros i j Hi Hj.
  rewrite entry_Build_Matrix, entry_Build_Vector.
  strip_truncations.
  destruct (dec (i = j)) as [p|np].
  { destruct p.
    rewrite kronecker_delta_refl.
    rewrite rng_mult_one_l.
    f_ap; apply path_ishprop. }
  apply neq_iff_lt_or_gt in np.
  destruct np as [l | l].
  - rewrite (kronecker_delta_lt l).
    rewrite rng_mult_zero_l.
    by rewrite H.
  - rewrite (kronecker_delta_gt l).
    rewrite rng_mult_zero_l.
    rewrite <- (matrix_transpose_issymmetric M).
    rewrite entry_Build_Matrix.
    by rewrite H.
Defined.

(** A symmetric lower triangular matrix is diagonal. *)
Global Instance isdiagonal_lower_triangular_issymmetric {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsSymmetric M} `{!IsLowerTriangular M}
  : IsDiagonal M.
Proof.
  rewrite <- (matrix_transpose_issymmetric M).
  rapply isdiagonal_upper_triangular_issymmetric.
Defined.

(** Note that symmetric matrices do not form a subring (or subalgebra) but they do form a submodule of the module of matrices. *)

(** ** Skew-symmetric Matrices *)

(** A matrix is skew-symmetric when it is equal to the negation of its transpose. *)
Class IsSkewSymmetric {R : Ring@{i}} {n : nat} (M : Matrix@{i} R n n) : Type@{i}
  := matrix_transpose_isskewsymmetric : matrix_transpose M = matrix_negate M.

Arguments matrix_transpose_isskewsymmetric {R n} M {_}.

(** The zero matrix is skew-symmetric. *)
Global Instance isskewsymmetric_matrix_zero {R : Ring@{i}} {n : nat}
  : IsSkewSymmetric (matrix_zero R n n).
Proof.
  unfold IsSkewSymmetric.
  rewrite matrix_transpose_zero.
  symmetry.
  nrapply (rng_negate_zero (A:=matrix_ring R n)).
Defined.

(** The negation of a skew-symmetric matrix is skew-symmetric. *)
Global Instance isskewsymmetric_matrix_negate {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsSkewSymmetric M}
  : IsSkewSymmetric (matrix_negate M).
Proof.
  unfold IsSkewSymmetric.
  rewrite matrix_transpose_negate.
  f_ap.
Defined.

(** A scalar multiple of a skew-symmetric matrix is skew-symmetric. *)
Global Instance isskewsymmetric_matrix_scale {R : Ring@{i}} {n : nat}
  (r : R) (M : Matrix R n n) `{!IsSkewSymmetric M}
  : IsSkewSymmetric (matrix_lact r M).
Proof.
  unfold IsSkewSymmetric.
  rewrite matrix_transpose_lact.
  rhs_V nrapply (lm_neg (M:=Build_LeftModule _ (abgroup_matrix R n n) _) r M).
  f_ap.
Defined.

(** The transpose of a skew-symmetric matrix is skew-symmetric. *)
Global Instance isskewsymmetric_matrix_transpose {R : Ring@{i}} {n : nat}
  (M : Matrix R n n) `{!IsSkewSymmetric M}
  : IsSkewSymmetric (matrix_transpose M).
Proof.
  unfold IsSkewSymmetric.
  rewrite <- matrix_transpose_negate.
  f_ap.
Defined.

(** The sum of two skew-symmetric matrices is skew-symmetric. *)
Global Instance isskewsymmetric_matrix_plus {R : Ring@{i}} {n : nat}
  (M N : Matrix R n n) `{!IsSkewSymmetric M} `{!IsSkewSymmetric N}
  : IsSkewSymmetric (matrix_plus M N).
Proof.
  unfold IsSkewSymmetric.
  rewrite matrix_transpose_plus.
  rhs nrapply (grp_inv_op (G:=abgroup_matrix R n n)).
  rhs_V nrapply (AbelianGroup.ab_comm (A:=abgroup_matrix R n n)).
  f_ap.
Defined.

(** Skew-symmetric matrices degenerate to symmetric matrices in rings with characteristic 2. In odd characteristic the module of matrices can be decomposed into the direct sum of symmetric and skew-symmetric matrices. *)

Section MatrixCat.

  (** The wild category [MatrixCat R] of [R]-valued matrices. This category has natural numbers as objects and m x n matrices as the arrows between [m] and [n]. *)
  Definition MatrixCat (R : Ring) := nat.

  Global Instance isgraph_matrixcat {R : Ring} : IsGraph (MatrixCat R)
    := {| Hom := Matrix R |}.

  Global Instance is01cat_matrixcat {R : Ring} : Is01Cat (MatrixCat R).
  Proof.
    snrapply Build_Is01Cat.
    - exact (identity_matrix R).
    - intros l m n M N.
      exact (matrix_mult N M).
  Defined.

  Global Instance is2graph_matrixcat {R : Ring} : Is2Graph (MatrixCat R)
    := is2graph_paths _.

  (** MatrixCat R forms a strong 1-category. *)
  Global Instance is1catstrong_matrixcat {R : Ring} : Is1Cat_Strong (MatrixCat R).
  Proof.
    snrapply Build_Is1Cat_Strong.
    (* Most of the structure comes from typeclasses in WildCat.Paths. *)
    1-4: exact _.
    - apply (associative_matrix_mult R).
    - intros k l m n M N P. apply inverse. apply (associative_matrix_mult R).
    - apply right_identity_matrix_mult.
    - apply left_identity_matrix_mult.
  Defined.

(** TODO: Define HasEquivs for MatrixCat.  *)

End MatrixCat.
