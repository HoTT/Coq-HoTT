Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import WildCat.Core.

(** * Kernels of group homomorphisms *)

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Definition grp_kernel {A B : Group} (f : GroupHomomorphism A B) : NormalSubgroup A.
Proof.
  snrapply Build_NormalSubgroup.
  - srapply (Build_Subgroup' (fun x => f x = group_unit)).
    1: apply grp_homo_unit.
    intros x y p q; cbn in p, q; cbn.
    lhs nrapply grp_homo_op.
    rhs_V nrapply (grp_inv_r mon_unit).
    nrapply (ap011 (.*.) p).
    lhs nrapply grp_homo_inv.
    nrapply (ap (-)).
    exact q.
  - intros x y; cbn; intros p.
    lhs nrapply grp_homo_op.
    nrapply grp_moveR_Mg.
    rhs nrapply grp_unit_r.
    rhs_V nrapply grp_unit_l.
    nrapply grp_moveL_gV.
    lhs_V nrapply grp_homo_op.
    exact p.
Defined.

(** ** Corecursion principle for group kernels *)

Proposition grp_kernel_corec {A B G : Group} {f : A $-> B} (g : G $-> A)
            (h : f $o g == grp_homo_const) : G $-> grp_kernel f.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun x:G => (g x; h x)).
  - intros x x'.
    apply path_sigma_hprop; cbn.
    apply grp_homo_op.
Defined.

Theorem equiv_grp_kernel_corec `{Funext} {A B G : Group} {f : A $-> B}
  : (G $-> grp_kernel f) <~> (exists g : G $-> A, f $o g == grp_homo_const).
Proof.
  srapply equiv_adjointify.
  - intro k.
    srefine (_ $o k; _).
    1: apply subgroup_incl.
    intro x; cbn.
    exact (k x).2.
  - intros [g p].
    exact (grp_kernel_corec _ p).
  - intros [g p].
    apply path_sigma_hprop; unfold pr1.
    apply equiv_path_grouphomomorphism; intro; reflexivity.
  - intro k.
    apply equiv_path_grouphomomorphism; intro x.
    apply path_sigma_hprop; reflexivity.
Defined.

(** ** Characterisation of group embeddings *)
Proposition equiv_kernel_isembedding `{Univalence} {A B : Group} (f : A $-> B)
  : (grp_kernel f = trivial_subgroup :> Subgroup A) <~> IsEmbedding f.
Proof.
  refine (_ oE (equiv_path_subgroup' _ _)^-1%equiv).
  apply equiv_iff_hprop_uncurried.
  refine (iff_compose _ (isembedding_grouphomomorphism f)); split.
  - intros E ? ?.
    by apply E.
  - intros e a; split.
    + apply e.
    + intro p.
      exact (ap _ p @ grp_homo_unit f).
Defined.
