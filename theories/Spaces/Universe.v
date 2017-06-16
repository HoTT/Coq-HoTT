(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import HProp UnivalenceImpliesFunext Fibrations.
Require Import Modalities.Modality HIT.Truncations HIT.Connectedness.
Import TrM.
Require Import Spaces.BAut Spaces.BAut.Rigid.
Require Import ExcludedMiddle.

Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * The universe *)

(** ** Automorphisms of the universe *)

(** If two inequivalent types have equivalent automorphism oo-groups, then assuming LEM we can swap them and leave the rest of the universe untouched. *)
Section SwapTypes.
  (** Amusingly, this does not actually require univalence!  But of course, to verify [BAut A <~> BAut B] in any particular example does require univalence. *)
  Context `{Funext} `{ExcludedMiddle}.
  Context (A B : Type) (ne : ~(A <~> B)) (e : BAut A <~> BAut B).

  Definition equiv_swap_types : Type <~> Type.
  Proof.
    refine (((equiv_decidable_sum (fun X:Type => merely (X=A)))^-1)
              oE _ oE
              (equiv_decidable_sum (fun X:Type => merely (X=A)))).
    refine ((equiv_functor_sum_l
               (equiv_decidable_sum (fun X => merely (X.1=B)))^-1)
              oE _ oE
              (equiv_functor_sum_l
                 (equiv_decidable_sum (fun X => merely (X.1=B))))).
    refine ((equiv_sum_assoc _ _ _)
              oE _ oE
              (equiv_sum_assoc _ _ _)^-1).
    apply equiv_functor_sum_r.
    assert (q : BAut B <~> {x : {x : Type & ~ merely (x = A)} &
                                merely (x.1 = B)}).
    { refine (equiv_sigma_assoc _ _ oE _).
      apply equiv_functor_sigma_id; intros X.
      apply equiv_iff_hprop.
      - intros p.
        refine (fun q => _ ; p).
        strip_truncations.
        destruct q.
        exact (ne (equiv_path X B p)).
      - exact pr2. }
    refine (_ oE equiv_sum_symm _ _).
    apply equiv_functor_sum'.
    - exact (e^-1 oE q^-1).
    - exact (q oE e).
  Defined.

  Definition equiv_swap_types_swaps : merely (equiv_swap_types A = B).
  Proof.
    assert (ea := (e (point _)).2). cbn in ea.
    strip_truncations; apply tr.
    unfold equiv_swap_types.
    apply moveR_equiv_V.
    rewrite (equiv_decidable_sum_l
               (fun X => merely (X=A)) A (tr 1)).
    assert (ne' : ~ merely (B=A))
      by (intros p; strip_truncations; exact (ne (equiv_path A B p^))).
    rewrite (equiv_decidable_sum_r
               (fun X => merely (X=A)) B ne').
    cbn.
    apply ap, path_sigma_hprop; cbn.
    exact ea.
  Defined.

  Definition equiv_swap_types_not_id
    : equiv_swap_types <> equiv_idmap.
  Proof.
    intros p.
    assert (q := equiv_swap_types_swaps).
    strip_truncations.
    apply ne.
    apply equiv_path.
    rewrite p in q; exact q.
  Qed.

End SwapTypes.

(** In particular, we can swap any two distinct rigid types. *)

Definition equiv_swap_rigid `{Univalence} `{ExcludedMiddle}
           (A B : Type) `{IsRigid A} `{IsRigid B} (ne : ~(A <~> B))
  : Type <~> Type.
Proof.
  refine (equiv_swap_types A B ne _).
  apply equiv_contr_contr.
Defined.

(** Such as [Empty] and [Unit]. *)

Definition equiv_swap_empty_unit `{Univalence} `{ExcludedMiddle}
  : Type <~> Type
  := equiv_swap_rigid Empty Unit (fun e => e^-1 tt).

(** We can also swap the products of two rigid types with another type [X], under a connectedness/truncatedness assumption. *)

Definition equiv_swap_prod_rigid  `{Univalence} `{ExcludedMiddle}
           (X A B : Type) (n : trunc_index) (ne : ~(X*A <~> X*B))
           `{IsRigid A} `{IsConnected n.+1 A}
           `{IsRigid B} `{IsConnected n.+1 B}
           `{IsTrunc n.+1 X}
  : Type <~> Type.
Proof.
  refine (equiv_swap_types (X*A) (X*B) ne _).
  transitivity (BAut X).
  - symmetry; exact (baut_prod_rigid_equiv X A n).
  - exact (baut_prod_rigid_equiv X B n).
Defined.
