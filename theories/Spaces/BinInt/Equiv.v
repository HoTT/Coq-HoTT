From HoTT Require Import Basics.
Require Import Spaces.Pos.
Require Import Spaces.BinInt.Core.
Require Import Spaces.BinInt.Spec.

(** ** Iteration of equivalences *)

(** *** Iteration by arbitrary integers *)

Definition binint_iter {A} (f : A -> A) `{!IsEquiv f} (n : BinInt) : A -> A
  := match n with
      | neg n => fun x => pos_iter f^-1 n x
      | zero => idmap
      | pos n => fun x => pos_iter f n x
     end.

(** Iteration by arbitrary integers requires the endofunction to be an equivalence, so that we can define a negative iteration by using its inverse. *)


Definition binint_iter_succ_l {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : BinInt) (a : A)
  : binint_iter f (binint_succ n) a = f (binint_iter f n a).
Proof.
  destruct n as [n| |n]; trivial.
  + revert n f H a.
    srapply pos_peano_ind.
    { intros f H a.
      symmetry.
      apply eisretr. }
    hnf; intros n p f H a.
    refine (ap (fun x => _ x _) _ @ _).
    1: rewrite binint_neg_pos_succ.
    1: exact (eisretr binint_succ (neg n)).
    apply moveL_equiv_M.
    cbn; symmetry.
    srapply pos_iter_succ_l.
  + cbn.
    rewrite pos_add_1_r.
    srapply pos_iter_succ_l.
Qed.

Definition binint_iter_succ_r {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : BinInt) (a : A) : binint_iter f (binint_succ n) a = binint_iter f n (f a).
Proof.
   destruct n as [n| |n]; trivial.
+ revert n f H a.
  srapply pos_peano_ind.
  { intros f H a.
    symmetry.
    apply eissect. }
  hnf; intros n p f H a.
  rewrite binint_neg_pos_succ.
  refine (ap (fun x => _ x _) _ @ _).
  1: exact (eisretr binint_succ (neg n)).
  cbn; rewrite pos_add_1_r.
  rewrite pos_iter_succ_r.
  rewrite eissect.
  reflexivity.
+ cbn.
  rewrite pos_add_1_r.
  srapply pos_iter_succ_r.
Qed.

Definition iter_binint_pred_l {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : BinInt) (a : A)
: binint_iter f (binint_pred n) a = f^-1 (binint_iter f n a).
Proof.
  destruct n as [n| |n]; trivial.
  + cbn; rewrite pos_add_1_r.
    by rewrite pos_iter_succ_l.
  + revert n.
    srapply pos_peano_ind.
    - cbn; symmetry; apply eissect.
    - hnf; intros p q.
      rewrite <- pos_add_1_r.
      change (binint_pred (pos (p + 1)%pos))
        with (binint_pred (binint_succ (pos p))).
      rewrite binint_pred_succ.
      change (pos (p + 1)%pos)
        with (binint_succ (pos p)).
      rewrite binint_iter_succ_l.
      symmetry.
      apply eissect.
Qed.

Definition iter_binint_pred_r {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : BinInt) (a : A)
: binint_iter f (binint_pred n) a = binint_iter f n (f^-1 a).
Proof.
  revert f H n a.
  destruct n as [n| |n]; trivial;
  induction n as [|n nH] using pos_peano_ind; trivial.
  2: hnf; intros; apply symmetry, eisretr.
  all: rewrite <- pos_add_1_r.
  all: intro a.
  1: change (neg (n + 1)%pos) with (binint_pred (neg n)).
  2: change (pos (n + 1)%pos) with (binint_succ (pos n)).
  1: rewrite <- 2 binint_neg_pos_succ.
  1: cbn; apply pos_iter_succ_r.
  rewrite binint_pred_succ.
  rewrite binint_iter_succ_r.
  rewrite eisretr.
  reflexivity.
Qed.

