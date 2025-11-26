From HoTT Require Import Basics.
Require Import Types.Universe.
Require Import Spaces.Pos.
Require Import Spaces.BinInt.Core.
Require Import Spaces.BinInt.Spec.
Require Import Spaces.BinInt.Equiv.

Local Open Scope positive_scope.
Local Open Scope binint_scope.

(** ** Exponentiation of loops *)

Definition loopexp_pos {A : Type} {x : A} (p : x = x) (n : Pos) : (x = x).
Proof.
  revert n.
  srapply pos_peano_ind.
  + exact p.
  + intros n q.
    exact (q @ p).
Defined.

Definition loopexp {A : Type} {x : A} (p : x = x) (z : BinInt) : (x = x)
  := match z with
       | neg n => loopexp_pos p^ n
       | zero => 1
       | pos n => loopexp_pos p n
     end.

(** TODO: One can also define [loopexp] as [int_iter (equiv_concat_r p x) z idpath].  This has slightly different computational behaviour, e.g., it sends [1 : int] to [1 @ p] rather than [p].  But with this definition, some of the results below become special cases of results in BinInt.Equiv, and others could be generalized to results belonging in BinInt.Equiv.  It's probably worth investigating this. *)

Lemma loopexp_pos_inv {A : Type} {x : A} (p : x = x) (n : Pos)
  : loopexp_pos p^ n = (loopexp_pos p n)^.
Proof.
  revert n.
  srapply pos_peano_ind; cbn; trivial.
  unfold loopexp_pos.
  intros n q.
  rewrite 2 pos_peano_ind_beta_pos_succ, q.
  refine ((inv_pp _ _)^ @ _).
  apply ap.
  clear q.
  revert n.
  srapply pos_peano_ind; cbn; trivial.
  intros n q.
  by rewrite pos_peano_ind_beta_pos_succ, concat_p_pp, q.
Qed.

Definition ap_loopexp_pos {A B} (f : A -> B) {x : A} (p : x = x) (n : Pos)
  : ap f (loopexp_pos p n) = loopexp_pos (ap f p) n.
Proof.
  revert n.
  srapply pos_peano_ind; cbn; trivial.
  unfold loopexp_pos.
  intros n q.
  rewrite 2 pos_peano_ind_beta_pos_succ.
  by rewrite ap_pp, q.
Qed.

Definition ap_loopexp {A B} (f : A -> B) {x : A} (p : x = x) (z : BinInt)
: ap f (loopexp p z) = loopexp (ap f p) z.
Proof.
  destruct z as [n| |n]; trivial.
  + cbn.
    rewrite loopexp_pos_inv, ap_V, loopexp_pos_inv.
    apply ap.
    apply ap_loopexp_pos.
  + apply ap_loopexp_pos.
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


Lemma loopexp_binint_pos_sub_l {A : Type} {x : A} (p : x = x) (a b : Pos)
  : loopexp p (binint_pos_sub a b) = loopexp_pos p^ b @ loopexp_pos p a.
Proof.
  symmetry.
  revert a b.
  induction a as [|a aH] using pos_peano_ind;
  induction b as [|b bH] using pos_peano_ind.
  + apply concat_Vp.
  + cbn; rewrite binint_pos_sub_succ_r.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    by rewrite concat_pp_p, concat_Vp, concat_p1.
  + rewrite binint_pos_sub_succ_l; cbn.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    rewrite loopexp_pos_concat.
    by rewrite concat_p_pp, concat_Vp, concat_1p.
  + rewrite binint_pos_sub_succ_succ.
    unfold loopexp_pos.
    rewrite 2 pos_peano_ind_beta_pos_succ.
    change ((loopexp_pos p^ b @ p^) @ (loopexp_pos p a @ p)
      = loopexp p (binint_pos_sub a b)).
    rewrite (loopexp_pos_concat p).
    rewrite concat_pp_p, (concat_p_pp p^ p).
    rewrite concat_Vp, concat_1p.
    apply aH.
Qed.

Lemma loopexp_binint_pos_sub_r {A : Type} {x : A} (p : x = x) (a b : Pos)
  : loopexp p (binint_pos_sub a b) = loopexp_pos p a @ loopexp_pos p^ b.
Proof.
  symmetry.
  revert a b.
  induction a as [|a aH] using pos_peano_ind;
  induction b as [|b bH] using pos_peano_ind.
  + apply concat_pV.
  + cbn; rewrite binint_pos_sub_succ_r.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    change (p @ (loopexp_pos p^ b @ p^) = loopexp p (neg b)).
    rewrite loopexp_pos_concat.
    by rewrite concat_p_pp, concat_pV, concat_1p.
  + rewrite binint_pos_sub_succ_l; cbn.
    unfold loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    change ((loopexp_pos p a @ p) @ p^ = loopexp_pos p a).
    by rewrite concat_pp_p, concat_pV, concat_p1.
  + rewrite binint_pos_sub_succ_succ.
    unfold loopexp_pos.
    rewrite 2 pos_peano_ind_beta_pos_succ.
    change ((loopexp_pos p a @ p) @ (loopexp_pos p^ b @ p^)
      = loopexp p (binint_pos_sub a b)).
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
  1: apply loopexp_binint_pos_sub_l.
  apply loopexp_binint_pos_sub_r.
Qed.

(** Under univalence, exponentiation of loops corresponds to iteration of auto-equivalences. *)

Definition equiv_path_loopexp
           {A : Type} (p : A = A) (z : BinInt) (a : A)
  : equiv_path A A (loopexp p z) a = binint_iter (equiv_path A A p) z a.
Proof.
  destruct z as [n| |n]; trivial.
  all: induction n as [|n IH]
    using pos_peano_ind; try reflexivity; cbn in *.
  all: unfold loopexp_pos; rewrite pos_peano_ind_beta_pos_succ.
  all: unfold pos_iter; rewrite pos_peano_rec_beta_pos_succ.
  all: refine (transport_pp _ _ _ _ @ _); cbn; apply ap, IH.
Defined.

Definition loopexp_path_universe `{Univalence}
           {A : Type} (f : A <~> A) (z : BinInt) (a : A)
  : transport idmap (loopexp (path_universe f) z) a
  = binint_iter f z a.
Proof.
  revert f. equiv_intro (equiv_path A A) p.
  refine (_ @ equiv_path_loopexp p z a).
  refine (ap (fun q => equiv_path A A (loopexp q z) a) _).
  apply eissect.
Defined.
