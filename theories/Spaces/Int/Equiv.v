Require Import Basics.
Require Import Spaces.Pos.
Require Import Spaces.Int.Core.
Require Import Spaces.Int.Spec.

(** ** Iteration of equivalences *)

(** *** Iteration by arbitrary integers *)

Definition int_iter {A} (f : A -> A) `{!IsEquiv f} (n : Int) : A -> A
  := match n with
      | neg n => fun x => pos_iter f^-1 n x
      | zero => idmap
      | pos n => fun x => pos_iter f n x
     end.

(** Iteration by arbitrary integers requires the endofunction to be an equivalence, so that we can define a negative iteration by using its inverse. *)


Definition int_iter_succ_l {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : Int) (a : A)
  : int_iter f (int_succ n) a = f (int_iter f n a).
Proof.
  destruct n as [n| |n]; trivial.
  + revert n f H a.
    serapply pos_peano_ind.
    { intros f H a.
      symmetry.
      apply eisretr. }
    hnf; intros n p f H a.
    refine (ap (fun x => _ x _) _ @ _).
    1: rewrite int_neg_pos_succ.
    1: exact (eisretr int_succ (neg n)).
    apply moveL_equiv_M.
    cbn; symmetry.
    serapply pos_iter_succ_l.
  + cbn.
    rewrite pos_add_1_r.
    serapply pos_iter_succ_l.
Qed.

Definition int_iter_succ_r {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : Int) (a : A) : int_iter f (int_succ n) a = int_iter f n (f a).
Proof.
   destruct n as [n| |n]; trivial.
+ revert n f H a.
  serapply pos_peano_ind.
  { intros f H a.
    symmetry.
    apply eissect. }
  hnf; intros n p f H a.
  rewrite int_neg_pos_succ.
  refine (ap (fun x => _ x _) _ @ _).
  1: exact (eisretr int_succ (neg n)).
  cbn; rewrite pos_add_1_r.
  rewrite pos_iter_succ_r.
  rewrite eissect.
  reflexivity.
+ cbn.
  rewrite pos_add_1_r.
  serapply pos_iter_succ_r.
Qed.

Definition iter_int_pred_l {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : Int) (a : A)
: int_iter f (int_pred n) a = f^-1 (int_iter f n a).
Proof.
  destruct n as [n| |n]; trivial.
  + cbn; rewrite pos_add_1_r.
    by rewrite pos_iter_succ_l.
  + revert n.
    serapply pos_peano_ind.
    - cbn; symmetry; apply eissect.
    - hnf; intros p q.
      rewrite <- pos_add_1_r.
      change (int_pred (pos (p + 1)%pos))
        with (int_pred (int_succ (pos p))).
      rewrite int_pred_succ.
      change (pos (p + 1)%pos)
        with (int_succ (pos p)).
      rewrite int_iter_succ_l.
      symmetry.
      apply eissect.
Qed.

Definition iter_int_pred_r {A} (f : A -> A) `{IsEquiv _ _ f}
  (n : Int) (a : A)
: int_iter f (int_pred n) a = int_iter f n (f^-1 a).
Proof.
  revert f H n a.
  destruct n as [n| |n]; trivial;
  induction n as [|n nH] using pos_peano_ind; trivial.
  2: hnf; intros; apply symmetry, eisretr.
  all: rewrite <- pos_add_1_r.
  all: intro a.
  1: change (neg (n + 1)%pos) with (int_pred (neg n)).
  2: change (pos (n + 1)%pos) with (int_succ (pos n)).
  1: rewrite <- 2 int_neg_pos_succ.
  1: cbn; apply pos_iter_succ_r.
  rewrite int_pred_succ.
  rewrite int_iter_succ_r.
  rewrite eisretr.
  reflexivity.
Qed.

