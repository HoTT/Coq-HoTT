Require Import Basics.
Require Import Types.Universe.
Require Import Spaces.Pos.
Require Import Spaces.Int.Core.
Require Import Spaces.Int.Spec.
Require Import Spaces.Int.Equiv.

Local Open Scope positive_scope.
Local Open Scope int_scope.

(** ** Exponentiation of loops *)

Definition loopexp_pos {A : Type} {x : A} (p : x = x) (n : Pos) : (x = x).
Proof.
  revert n.
  serapply pos_peano_ind.
  + exact p.
  + intros n q.
    exact (q @ p).
Defined.

Definition loopexp {A : Type} {x : A} (p : x = x) (z : Int) : (x = x)
  := match z with
       | neg n => loopexp_pos p^ n
       | zero => 1
       | pos n => loopexp_pos p n
     end.

Lemma loopexp_pos_inv {A : Type} {x : A} (p : x = x) (n : Pos)
  : loopexp_pos p^ n = (loopexp_pos p n)^.
Proof.
  revert n.
  serapply pos_peano_ind; cbn; trivial.
  unfold loopexp_pos.
  intros n q.
  rewrite 2 pos_peano_ind_beta_pos_succ, q.
  refine ((inv_pp _ _)^ @ _).
  apply ap.
  clear q.
  revert n.
  serapply pos_peano_ind; cbn; trivial.
  intros n q.
  by rewrite pos_peano_ind_beta_pos_succ, concat_p_pp, q.
Qed.

Definition ap_loopexp_pos {A B} (f : A -> B) {x : A} (p : x = x) (n : Pos)
  : ap f (loopexp_pos p n) = loopexp_pos (ap f p) n.
Proof.
  revert n.
  serapply pos_peano_ind; cbn; trivial.
  unfold loopexp_pos.
  intros n q.
  rewrite 2 pos_peano_ind_beta_pos_succ.
  by rewrite ap_pp, q.
Qed.

Definition ap_loopexp {A B} (f : A -> B) {x : A} (p : x = x) (z : Int)
: ap f (loopexp p z) = loopexp (ap f p) z.
Proof.
  destruct z as [n| |n]; trivial.
  + cbn.
    rewrite loopexp_pos_inv, ap_V, loopexp_pos_inv.
    apply ap.
    apply ap_loopexp_pos.
  + apply ap_loopexp_pos.
Qed.

Lemma int_add_succ_l a b : int_succ a + b = int_succ (a + b).
Proof.
  rewrite <- int_add_assoc, (int_add_comm 1 b).
  apply int_add_assoc.
Qed.

Lemma int_add_succ_r a b : a + int_succ b = int_succ (a + b).
Proof.
  apply int_add_assoc.
Qed.

Lemma int_add_pred_l a b : int_pred a + b = int_pred (a + b).
Proof.
  rewrite <- int_add_assoc, (int_add_comm (-1) b).
  apply int_add_assoc.
Qed.

Lemma int_add_pred_r a b : a + int_pred b = int_pred (a + b).
Proof.
  apply int_add_assoc.
Qed.

Lemma loopexp_pos_concat {A : Type} {x : A} (p : x = x) (a : Pos)
  : loopexp_pos p a @ p = p @ loopexp_pos p a.
Proof.
  induction a as [|a aH] using pos_peano_ind; trivial.
  unfold loopexp_pos.
  rewrite pos_peano_ind_beta_pos_succ.
  change ((loopexp_pos p a @ p) @ p = p @ (loopexp_pos p a @ p)).
  by rewrite concat_p_pp, aH.
Qed.

Lemma loopexp_pos_add {A : Type} {x : A} (p : x = x) (a b : Pos)
  : loopexp_pos p (a + b)%pos = loopexp_pos p a @ loopexp_pos p b.
Proof.
  revert a b.
  induction a as [|a aH] using pos_peano_ind;
  induction b as [|b bH] using pos_peano_ind;
  trivial.
  + rewrite pos_add_1_l in *.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    change (loopexp_pos p (pos_succ b) @ p
      = p @ loopexp_pos p (pos_succ b)).
    rewrite bH; cbn.
    by rewrite concat_pp_p, loopexp_pos_concat.
  + rewrite pos_add_1_r in *.
    unfold loopexp_pos.
    by rewrite pos_peano_ind_beta_pos_succ.
  + rewrite pos_add_succ_l.
    unfold loopexp_pos.
    rewrite 2 pos_peano_ind_beta_pos_succ.
    change (loopexp_pos p (a + pos_succ b)%pos @ p
      = (loopexp_pos p a @ p) @ loopexp_pos p (pos_succ b)).
    by rewrite aH, 2 concat_pp_p, loopexp_pos_concat.
Qed.


Lemma loopexp_int_pos_sub_l {A : Type} {x : A} (p : x = x) (a b : Pos)
  : loopexp p (int_pos_sub a b) = loopexp_pos p^ b @ loopexp_pos p a.
Proof.
  symmetry.
  revert a b.
  induction a as [|a aH] using pos_peano_ind;
  induction b as [|b bH] using pos_peano_ind.
  + apply concat_Vp.
  + cbn; rewrite int_pos_sub_succ_r.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    by rewrite concat_pp_p, concat_Vp, concat_p1.
  + rewrite int_pos_sub_succ_l; cbn.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    rewrite loopexp_pos_concat.
    by rewrite concat_p_pp, concat_Vp, concat_1p.
  + rewrite int_pos_sub_succ_succ.
    unfold loopexp_pos.
    rewrite 2 pos_peano_ind_beta_pos_succ.
    change ((loopexp_pos p^ b @ p^) @ (loopexp_pos p a @ p)
      = loopexp p (int_pos_sub a b)).
    rewrite (loopexp_pos_concat p).
    rewrite concat_pp_p, (concat_p_pp p^ p).
    rewrite concat_Vp, concat_1p.
    apply aH.
Qed.

Lemma loopexp_int_pos_sub_r {A : Type} {x : A} (p : x = x) (a b : Pos)
  : loopexp p (int_pos_sub a b) = loopexp_pos p a @ loopexp_pos p^ b.
Proof.
  symmetry.
  revert a b.
  induction a as [|a aH] using pos_peano_ind;
  induction b as [|b bH] using pos_peano_ind.
  + apply concat_pV.
  + cbn; rewrite int_pos_sub_succ_r.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    change (p @ (loopexp_pos p^ b @ p^) = loopexp p (neg b)).
    rewrite loopexp_pos_concat.
    by rewrite concat_p_pp, concat_pV, concat_1p.
  + rewrite int_pos_sub_succ_l; cbn.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    change ((loopexp_pos p a @ p) @ p^ = loopexp_pos p a).
    by rewrite concat_pp_p, concat_pV, concat_p1.
  + rewrite int_pos_sub_succ_succ.
    unfold loopexp_pos.
    rewrite 2 pos_peano_ind_beta_pos_succ.
    change ((loopexp_pos p a @ p) @ (loopexp_pos p^ b @ p^)
      = loopexp p (int_pos_sub a b)).
    rewrite (loopexp_pos_concat p^).
    rewrite concat_pp_p, (concat_p_pp p p^).
    rewrite concat_pV, concat_1p.
    apply aH.
Qed.

Lemma loopexp_add {A : Type} {x : A} (p : x = x) a b
  : loopexp p (a + b) = loopexp p a @ loopexp p b.
Proof.
  destruct a as [a| |a], b as [b| |b]; trivial;
  try apply loopexp_pos_add; cbn.
  1,6: symmetry; apply concat_p1.
  2,3: symmetry; apply concat_1p.
  1: apply loopexp_int_pos_sub_l.
  apply loopexp_int_pos_sub_r.
Qed.

(** Under univalence, exponentiation of loops corresponds to iteration of autoequivalences. *)

Definition equiv_path_loopexp `{Univalence}
           {A : Type} (p : A = A) (z : Int) (a : A)
  : equiv_path A A (loopexp p z) a = int_iter (equiv_path A A p) z a.
Proof.
  destruct z as [n| |n]; trivial.
  all: induction n as [|n IH]
    using pos_peano_ind; try reflexivity; cbn in *.
  all: unfold loopexp_pos; rewrite pos_peano_ind_beta_pos_succ.
  all: unfold pos_iter; rewrite pos_peano_ind_beta_pos_succ.
  all: refine (transport_pp _ _ _ _ @ _); cbn; apply ap, IH.
Defined.

Definition loopexp_path_universe `{Univalence}
           {A : Type} (f : A <~> A) (z : Int) (a : A)
  : transport idmap (loopexp (path_universe f) z) a
  = int_iter f z a.
Proof.
  revert f. equiv_intro (equiv_path A A) p.
  refine (_ @ equiv_path_loopexp p z a).
  refine (ap (fun q => equiv_path A A (loopexp q z) a) _).
  apply eissect.
Defined.