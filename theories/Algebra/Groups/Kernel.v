Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import WildCat.Core.
Require Import Universes.HSet.

(** * Kernels of group homomorphisms *)

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Definition grp_kernel {A B : Group} (f : GroupHomomorphism A B) : NormalSubgroup A.
Proof.
  snrapply Build_NormalSubgroup.
  - srapply (Build_Subgroup' (fun x => f x = 1)); cbn beta.
    1: apply grp_homo_unit.
    intros x y p q.
    apply (grp_homo_moveL_1M _ _ _)^-1.
    exact (p @ q^).
  - intros x y; cbn; intros p.
    apply (grp_homo_moveL_1V _ _ _)^-1.
    lhs_V nrapply grp_inv_inv.
    nrapply (ap (-) _^).
    by apply grp_homo_moveL_1V.
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

(** The underlying map of a group homomorphism with a trivial kernel is an embedding. *)
Global Instance isembedding_istrivial_kernel {G H : Group} (f : G $-> H)
  (triv : IsTrivialGroup (grp_kernel f))
  : IsEmbedding f.
Proof.
  intros h.
  apply hprop_allpath.
  intros [x p] [y q].
  srapply path_sigma_hprop; unfold pr1.
  apply grp_moveL_1M.
  apply triv; simpl.
  rhs_V nrapply (grp_inv_r h).
  lhs nrapply grp_homo_op.
  nrapply (ap011 (.*.) p).
  lhs nrapply grp_homo_inv.
  exact (ap (^) q).
Defined.

(** If the underlying map of a group homomorphism is an embedding then the kernel is trivial. *)
Definition istrivial_kernel_isembedding {G H : Group} (f : G $-> H)
  (emb : IsEmbedding f)
  : IsTrivialGroup (grp_kernel f).
Proof.
  intros g p.
  rapply (isinj_embedding f).
  exact (p @ (grp_homo_unit f)^).
Defined.
Global Hint Immediate istrivial_kernel_isembedding : typeclass_instances.

(** Characterisation of group embeddings *)
Proposition equiv_istrivial_kernel_isembedding `{F : Funext}
  {G H : Group} (f : G $-> H)
  : IsTrivialGroup (grp_kernel f) <~> IsEmbedding f.
Proof.
  apply equiv_iff_hprop_uncurried.
  split; exact _.
Defined.
