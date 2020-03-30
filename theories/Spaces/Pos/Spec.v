Require Import Basics.
Require Import Pos.Core.

Local Open Scope positive_scope.

(** ** Specification of [succ] in term of [add] *)

Lemma pos_add_1_r p : p + 1 = pos_succ p.
Proof.
  by destruct p.
Qed.

Lemma pos_add_1_l p : 1 + p = pos_succ p.
Proof.
  by destruct p.
Qed.

(** ** Specification of [add_carry] *)

Theorem pos_add_carry_spec p q : pos_add_carry p q = pos_succ (p + q).
Proof.
  revert q.
  induction p; destruct q; simpl; by apply ap.
Qed.

(** ** Commutativity of [add] *)

Theorem pos_add_comm p q : p + q = q + p.
Proof.
  revert q.
  induction p; destruct q; simpl; apply ap; trivial.
  rewrite 2 pos_add_carry_spec; by apply ap.
Qed.

(** ** Permutation of [add] and [succ] *)

Theorem pos_add_succ_r p q : p + pos_succ q = pos_succ (p + q).
Proof.
  revert q.
  induction p; destruct q; simpl; apply ap;
   auto using pos_add_1_r; rewrite pos_add_carry_spec; auto.
Qed.

Theorem pos_add_succ_l p q : pos_succ p + q = pos_succ (p + q).
Proof.
  rewrite pos_add_comm, (pos_add_comm p). apply pos_add_succ_r.
Qed.

Definition pos_add_succ p q : p + pos_succ q = pos_succ p + q.
Proof.
  by rewrite pos_add_succ_r, pos_add_succ_l.
Defined.

Definition pos_add_carry_spec_l q r
  : pos_add_carry q r = pos_succ q + r.
Proof.
  by rewrite pos_add_carry_spec, pos_add_succ_l.
Qed.

Definition pos_add_carry_spec_r q r
  : pos_add_carry q r = q + pos_succ r.
Proof.
  by rewrite pos_add_carry_spec, pos_add_succ_r.
Defined.

(** ** No neutral elements for addition *)
Lemma pos_add_no_neutral p q : q + p <> p.
Proof.
  revert q.
  induction p as [ |p IHp|p IHp]; intros [ |q|q].
  1,3: apply x0_neq_xH.
  1: apply x1_neq_xH.
  1,3: apply x1_neq_x0.
  2,4: apply x0_neq_x1.
  1,2: intro H; apply (IHp q).
  1: apply x0_inj, H.
  apply x1_inj, H.
Qed.

(** * Injectivity of pos_succ *)
Lemma pos_succ_inj n m : pos_succ n = pos_succ m -> n = m.
Proof.
  revert m.
  induction n as [ | n x | n x]; induction m as [ | m y | m y].
  + reflexivity.
  + intro p.
    destruct (x0_neq_x1 p).
  + intro p.
    simpl in p.
    apply x0_inj in p.
    destruct m.
    1,3: destruct (xH_neq_x0 p).
    destruct (xH_neq_x1 p).
  + intro p.
    destruct (x1_neq_x0 p).
  + simpl.
    intro p.
    by apply ap, x1_inj.
  + intro p.
    destruct (x1_neq_x0 p).
  + intro p.
    cbn in p.
    apply x0_inj in p.
    destruct n.
    1,3: destruct (x0_neq_xH p).
    destruct (x1_neq_xH p).
  + intro p.
    cbn in p.
    destruct (x0_neq_x1 p).
  + intro p.
    apply ap, x, x0_inj, p.
Defined.

(** ** Addition is associative *)

Theorem pos_add_assoc p q r : p + (q + r) = p + q + r.
Proof.
  revert q r.
  induction p.
  + intros [|q|q] [|r|r].
    all: try reflexivity.
    all: simpl.
    1,2: by destruct r.
    1,2: apply ap; symmetry.
    1: apply pos_add_carry_spec.
    1: apply pos_add_succ_l.
    apply ap.
    rewrite pos_add_succ_l.
    apply pos_add_carry_spec.
  + intros [|q|q] [|r|r].
    all: try reflexivity.
    all: cbn; apply ap.
    3,4,6: apply IHp.
    1: apply pos_add_1_r.
    1: symmetry; apply pos_add_carry_spec_r.
    1: apply pos_add_succ_r.
    rewrite 2 pos_add_carry_spec_l.
    rewrite <- pos_add_succ_r.
    apply IHp.
  + intros [|q|q] [|r|r].
    all: cbn; apply ap.
    1: apply pos_add_1_r.
    1: apply pos_add_carry_spec_l.
    1: apply pos_add_succ.
    1: apply pos_add_carry_spec.
    1: apply IHp.
    2: symmetry; apply pos_add_carry_spec_r.
    1,2: rewrite 2 pos_add_carry_spec, ?pos_add_succ_l.
    1,2: apply ap, IHp.
    rewrite ?pos_add_carry_spec_r.
    rewrite pos_add_succ.
    apply IHp.
Qed.

(** ** One is neutral for multiplication *)

Lemma pos_mul_1_l p : 1 * p = p.
Proof.
  reflexivity.
Qed.

Lemma pos_mul_1_r p : p * 1 = p.
Proof.
  induction p; cbn; trivial; by apply ap.
Qed.

(** pos_succ and doubling functions *)

Lemma pos_pred_double_succ n
  : pos_pred_double (pos_succ n) = n~1.
Proof.
  induction n as [|n|n nH].
  all: trivial.
  cbn; apply ap, nH.
Qed.

Lemma pos_succ_pred_double n
  : pos_succ (pos_pred_double n) = n~0.
Proof.
  induction n as [|n nH|n].
  all: trivial.
  cbn; apply ap, nH.
Qed.

(** ** Iteration and pos_succ *)
Lemma pos_iter_succ_l {A} (f : A -> A) p a
  : pos_iter f (pos_succ p) a = f (pos_iter f p a).
Proof.
  unfold pos_iter.
  by rewrite pos_peano_ind_beta_pos_succ.
Qed.

Lemma pos_iter_succ_r {A} (f : A -> A) p a
  : pos_iter f (pos_succ p) a = pos_iter f p (f a).
Proof.
  revert p f a.
  srapply pos_peano_ind.
  1: hnf; intros; trivial.
  hnf; intros p q f a.
  refine (_ @ _ @ _^).
  1,3: unfold pos_iter;
    by rewrite pos_peano_ind_beta_pos_succ.
  apply ap.
  apply q.
Qed.

(** ** Right reduction properties for multiplication *)
Lemma mul_xO_r p q : p * q~0 = (p * q)~0.
Proof.
  induction p; simpl; f_ap; f_ap; trivial.
Qed.

Lemma mul_xI_r p q : p * q~1 = p + (p * q)~0.
Proof.
  induction p; simpl; trivial; f_ap.
  rewrite IHp.
  rewrite pos_add_assoc.
  rewrite (pos_add_comm q p).
  symmetry.
  apply pos_add_assoc.
Qed.

(** ** Commutativity of multiplication *)
Lemma pos_mul_comm p q : p * q = q * p.
Proof.
  induction q; simpl.
  1: apply pos_mul_1_r.
  + rewrite mul_xO_r.
    f_ap.
  + rewrite mul_xI_r.
    f_ap; f_ap.
Qed.

(** ** Distributivity of addition over multiplication *)
Theorem pos_mul_add_distr_l p q r :
  p * (q + r) = p * q + p * r.
Proof.
  induction p; cbn; [reflexivity | f_ap | ].
  rewrite IHp.
  set (m:=(p*q)~0).
  set (n:=(p*r)~0).
  change ((p*q+p*r)~0) with (m+n).
  rewrite 2 pos_add_assoc; f_ap.
  rewrite <- 2 pos_add_assoc; f_ap.
  apply pos_add_comm.
Qed.

Theorem pos_mul_add_distr_r p q r :
  (p + q) * r = p * r + q * r.
Proof.
  rewrite 3 (pos_mul_comm _ r); apply pos_mul_add_distr_l.
Qed.

(** ** Associativity of multiplication *)
Theorem pos_mul_assoc p q r : p * (q * r) = p * q * r.
Proof.
  induction p; simpl; rewrite ?IHp; trivial.
  by rewrite pos_mul_add_distr_r.
Qed.

(** ** pos_succ and pos_mul *)

Lemma pos_mul_succ_l p q
  : (pos_succ p) * q = p * q + q.
Proof.
  by rewrite <- pos_add_1_r, pos_mul_add_distr_r, pos_mul_1_l.
Qed.

Lemma pos_mul_succ_r p q
  : p * (pos_succ q) = p + p * q.
Proof.
  by rewrite <- pos_add_1_l, pos_mul_add_distr_l, pos_mul_1_r.
Qed.
